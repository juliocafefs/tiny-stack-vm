// A tiny stack VM for make.fun's tiny stack ISA v1, following the ISA's
// reference semantics exactly: wrapping 32-bit arithmetic, unsigned ops
// read as unsigned, masked shift counts, every trap with its own exit
// code, the step limit and the output limit.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Runs one program on one input; returns [output bytes, exit code]. A trap
// ends the run with the trap's number as its code, keeping prior output.
function exec(P, inp) {
  const st = new Int32Array(256); // data stack, at most 256 values
  const cs = new Int32Array(64); // return addresses, at most 64
  const mem = new Int32Array(256); // memory words 0..255, zero at first
  const buf = new Uint8Array(65536); // output, at most 65,536 bytes
  let sp = 0, cp = 0, pc = 0, ip = 0, ol = 0, steps = 0;
  const end = (code) => [buf.slice(0, ol), code];
  for (;;) {
    // Checks in the ISA's order: step limit, pc in bounds, opcode known,
    // immediate fits, then the stack needs, then the instruction acts.
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= P.length) return end(9);
    const op = P[pc];
    // Immediate lengths: PUSH8 1 byte, PUSH32 4, jumps and CALL 2, else 0.
    const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    if (!(op <= 7 || (op >= 0x10 && op <= 0x1e) || (op >= 0x20 && op <= 0x22) ||
      (op >= 0x30 && op <= 0x34) || op === 0x40 || op === 0x41 || (op >= 0x50 && op <= 0x53))) return end(5);
    if (pc + imm >= P.length) return end(9);
    steps++;
    const nx = pc + 1 + imm;
    pc = nx;
    switch (op) {
      case 0x00:
        return end(0);
      case 0x01: // PUSH8, sign-extended
        if (sp === 256) return end(3);
        st[sp++] = (P[nx - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32, little-endian
        if (sp === 256) return end(3);
        st[sp++] = P[nx - 4] | (P[nx - 3] << 8) | (P[nx - 2] << 16) | (P[nx - 1] << 24);
        break;
      case 0x03:
        if (sp === 0) return end(2);
        sp--;
        break;
      case 0x04: // DUP
        if (sp === 0) return end(2);
        if (sp === 256) return end(3);
        st[sp] = st[sp - 1];
        sp++;
        break;
      case 0x05: { // SWAP
        if (sp < 2) return end(2);
        const t = st[sp - 1];
        st[sp - 1] = st[sp - 2];
        st[sp - 2] = t;
        break;
      }
      case 0x06: // OVER
        if (sp < 2) return end(2);
        if (sp === 256) return end(3);
        st[sp] = st[sp - 2];
        sp++;
        break;
      case 0x07: { // ROT: ( a b c -- b c a )
        if (sp < 3) return end(2);
        const a = st[sp - 3];
        st[sp - 3] = st[sp - 2];
        st[sp - 2] = st[sp - 1];
        st[sp - 1] = a;
        break;
      }
      case 0x17: // NEG, wraps: -(-2147483648) is -2147483648
        if (sp === 0) return end(2);
        st[sp - 1] = -st[sp - 1] | 0;
        break;
      case 0x1b:
        if (sp === 0) return end(2);
        st[sp - 1] = ~st[sp - 1];
        break;
      case 0x30: // JMP, JZ, JNZ: target = next + signed offset
      case 0x31:
      case 0x32: {
        const rel = ((P[nx - 2] | (P[nx - 1] << 8)) << 16) >> 16;
        if (op === 0x30) pc = nx + rel;
        else {
          if (sp === 0) return end(2);
          const v = st[--sp];
          if ((op === 0x31) === (v === 0)) pc = nx + rel;
        }
        break;
      }
      case 0x33: // CALL: unsigned absolute address
        if (cp === 64) return end(7);
        cs[cp++] = nx;
        pc = P[nx - 2] | (P[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return end(8);
        pc = cs[--cp];
        break;
      case 0x40: { // LOAD
        if (sp === 0) return end(2);
        const a = st[sp - 1];
        if (a < 0 || a > 255) return end(6);
        st[sp - 1] = mem[a];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        if (sp < 2) return end(2);
        const a = st[sp - 1];
        if (a < 0 || a > 255) return end(6);
        mem[a] = st[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no padding or newline
        if (sp === 0) return end(2);
        const s = String(st[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let k = 0; k < s.length; k++) buf[ol++] = s.charCodeAt(k);
        break;
      }
      case 0x51: // PUTC: one byte, the low 8 bits
        if (sp === 0) return end(2);
        if (ol === 65536) return end(11);
        buf[ol++] = st[--sp] & 255;
        break;
      case 0x52: // IN: next input byte, -1 once used up
        if (sp === 256) return end(3);
        st[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53: // EXIT: code is the low 8 bits
        if (sp === 0) return end(2);
        return end(st[sp - 1] & 255);
      default: {
        // Two-operand ops ( a b -- r ), b on top: 0x10-0x1e, 0x20-0x22.
        if (sp < 2) return end(2);
        const b = st[sp - 1];
        const a = st[sp - 2];
        let r;
        if (op === 0x10) r = a + b | 0;
        else if (op === 0x11) r = a - b | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op >= 0x13 && op <= 0x16) {
          if (b === 0) return end(4);
          r = op === 0x13 ? (a / b) | 0 : op === 0x14 ? a % b | 0 :
            op === 0x15 ? Math.floor((a >>> 0) / (b >>> 0)) | 0 : (a >>> 0) % (b >>> 0) | 0;
        }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        st[sp - 2] = r;
        sp--;
        break;
      }
    }
  }
}

for (const id of readdirSync(I).sort()) {
  const [out, code] = exec(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), code + '\n');
}
