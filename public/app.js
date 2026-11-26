/* ============================================================================
   1. SHARED CHESS CORE (Used by Main Thread & Inline Web Worker)
   ============================================================================ */
function createChessCore() {
  const EMPTY = 0;
  const WP = 1, WN = 2, WB = 3, WR = 4, WQ = 5, WK = 6;
  const BP = -1, BN = -2, BB = -3, BR = -4, BQ = -5, BK = -6;

  const FLAG_EP = 1;
  const FLAG_CASTLE = 2;
  const FLAG_CAPTURE = 4;

  const CASTLE_MASK = new Uint8Array(64).fill(15);
  CASTLE_MASK[0] = 15 & ~8;
  CASTLE_MASK[4] = 15 & ~12;
  CASTLE_MASK[7] = 15 & ~4;
  CASTLE_MASK[56] = 15 & ~2;
  CASTLE_MASK[60] = 15 & ~3;
  CASTLE_MASK[63] = 15 & ~1;

  // 64-bit Zobrist Hashing (two 32-bit unsigned ints)
  let seed = 0x9e3779b9;
  function rand32() {
    seed ^= seed << 13;
    seed ^= seed >>> 17;
    seed ^= seed << 5;
    return seed >>> 0;
  }

  const zPieceLo = new Uint32Array(13 * 64);
  const zPieceHi = new Uint32Array(13 * 64);
  for (let i = 0; i < 13 * 64; i++) {
    zPieceLo[i] = rand32();
    zPieceHi[i] = rand32();
  }
  const zCastleLo = new Uint32Array(16);
  const zCastleHi = new Uint32Array(16);
  for (let i = 0; i < 16; i++) {
    zCastleLo[i] = rand32();
    zCastleHi[i] = rand32();
  }
  const zEpLo = new Uint32Array(65);
  const zEpHi = new Uint32Array(65);
  for (let i = 0; i < 65; i++) {
    zEpLo[i] = rand32();
    zEpHi[i] = rand32();
  }
  const zSideLo = rand32();
  const zSideHi = rand32();

  function encodeMove(from, to, promo = 0, flags = 0) {
    return from | (to << 6) | (promo << 12) | (flags << 15);
  }

  function sqToAlgebraic(sq) {
    return 'abcdefgh'[sq & 7] + (8 - (sq >> 3));
  }

  function moveToUci(m) {
    const from = m & 63;
    const to = (m >> 6) & 63;
    const promo = (m >> 12) & 7;
    const pChar = promo ? ['', '', 'n', 'b', 'r', 'q'][promo] : '';
    return sqToAlgebraic(from) + sqToAlgebraic(to) + pChar;
  }

  function computeHash(state) {
    let lo = 0, hi = 0;
    const b = state.board;
    for (let sq = 0; sq < 64; sq++) {
      const p = b[sq];
      if (p !== 0) {
        const idx = (p + 6) * 64 + sq;
        lo ^= zPieceLo[idx];
        hi ^= zPieceHi[idx];
      }
    }
    lo ^= zCastleLo[state.castling];
    hi ^= zCastleHi[state.castling];
    const epIdx = state.ep === -1 ? 64 : state.ep;
    lo ^= zEpLo[epIdx];
    hi ^= zEpHi[epIdx];
    if (state.turn === -1) {
      lo ^= zSideLo;
      hi ^= zSideHi;
    }
    state.hLo = lo >>> 0;
    state.hHi = hi >>> 0;
  }

  function createInitialState() {
    const board = new Int8Array([
      BR, BN, BB, BQ, BK, BB, BN, BR,
      BP, BP, BP, BP, BP, BP, BP, BP,
      0,  0,  0,  0,  0,  0,  0,  0,
      0,  0,  0,  0,  0,  0,  0,  0,
      0,  0,  0,  0,  0,  0,  0,  0,
      0,  0,  0,  0,  0,  0,  0,  0,
      WP, WP, WP, WP, WP, WP, WP, WP,
      WR, WN, WB, WQ, WK, WB, WN, WR
    ]);
    const state = {
      board,
      turn: 1,
      castling: 15,
      ep: -1,
      halfmove: 0,
      fullmove: 1,
      wKing: 60,
      bKing: 4,
      hLo: 0,
      hHi: 0
    };
    computeHash(state);
    return state;
  }

  function cloneState(s) {
    return {
      board: new Int8Array(s.board),
      turn: s.turn,
      castling: s.castling,
      ep: s.ep,
      halfmove: s.halfmove,
      fullmove: s.fullmove,
      wKing: s.wKing,
      bKing: s.bKing,
      hLo: s.hLo,
      hHi: s.hHi
    };
  }

  const KNIGHT_DR = [-2, -2, -1, -1, 1, 1, 2, 2];
  const KNIGHT_DC = [-1, 1, -2, 2, -2, 2, -1, 1];
  const KING_DR = [-1, -1, -1, 0, 0, 1, 1, 1];
  const KING_DC = [-1, 0, 1, -1, 1, -1, 0, 1];
  const DIAG_DR = [-1, -1, 1, 1];
  const DIAG_DC = [-1, 1, -1, 1];
  const ORTHO_DR = [-1, 1, 0, 0];
  const ORTHO_DC = [0, 0, -1, 1];

  function isSquareAttacked(state, sq, byColor) {
    const b = state.board;
    const r = sq >> 3;
    const c = sq & 7;

    const pr = byColor === 1 ? r + 1 : r - 1;
    if (pr >= 0 && pr < 8) {
      const targetPawn = byColor * WP;
      if (c > 0 && b[(pr << 3) | (c - 1)] === targetPawn) return true;
      if (c < 7 && b[(pr << 3) | (c + 1)] === targetPawn) return true;
    }

    const targetKnight = byColor * WN;
    for (let i = 0; i < 8; i++) {
      const nr = r + KNIGHT_DR[i];
      const nc = c + KNIGHT_DC[i];
      if ((nr | nc) >= 0 && nr < 8 && nc < 8) {
        if (b[(nr << 3) | nc] === targetKnight) return true;
      }
    }

    const targetKing = byColor * WK;
    for (let i = 0; i < 8; i++) {
      const nr = r + KING_DR[i];
      const nc = c + KING_DC[i];
      if ((nr | nc) >= 0 && nr < 8 && nc < 8) {
        if (b[(nr << 3) | nc] === targetKing) return true;
      }
    }

    const targetB = byColor * WB;
    const targetQ = byColor * WQ;
    for (let d = 0; d < 4; d++) {
      let nr = r + DIAG_DR[d];
      let nc = c + DIAG_DC[d];
      while (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
        const p = b[(nr << 3) | nc];
        if (p !== 0) {
          if (p === targetB || p === targetQ) return true;
          break;
        }
        nr += DIAG_DR[d];
        nc += DIAG_DC[d];
      }
    }

    const targetR = byColor * WR;
    for (let d = 0; d < 4; d++) {
      let nr = r + ORTHO_DR[d];
      let nc = c + ORTHO_DC[d];
      while (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
        const p = b[(nr << 3) | nc];
        if (p !== 0) {
          if (p === targetR || p === targetQ) return true;
          break;
        }
        nr += ORTHO_DR[d];
        nc += ORTHO_DC[d];
      }
    }

    return false;
  }

  function inCheck(state, color) {
    const kSq = color === 1 ? state.wKing : state.bKing;
    return isSquareAttacked(state, kSq, -color);
  }

  function generatePseudoMoves(state, buf, offset, capturesOnly) {
    const b = state.board;
    const turn = state.turn;
    let idx = offset;

    for (let sq = 0; sq < 64; sq++) {
      const p = b[sq];
      if (p === 0 || (p > 0 ? 1 : -1) !== turn) continue;
      const type = p > 0 ? p : -p;
      const r = sq >> 3;
      const c = sq & 7;

      if (type === WP) {
        const dir = turn === 1 ? -1 : 1;
        const startRow = turn === 1 ? 6 : 1;
        const promoRow = turn === 1 ? 0 : 7;
        const nr = r + dir;

        if (nr >= 0 && nr < 8) {
          for (let dc = -1; dc <= 1; dc += 2) {
            const nc = c + dc;
            if (nc < 0 || nc > 7) continue;
            const to = (nr << 3) | nc;
            const target = b[to];
            if (target !== 0 && (target > 0 ? 1 : -1) === -turn) {
              if (nr === promoRow) {
                buf[idx++] = encodeMove(sq, to, WQ, FLAG_CAPTURE);
                buf[idx++] = encodeMove(sq, to, WR, FLAG_CAPTURE);
                buf[idx++] = encodeMove(sq, to, WB, FLAG_CAPTURE);
                buf[idx++] = encodeMove(sq, to, WN, FLAG_CAPTURE);
              } else {
                buf[idx++] = encodeMove(sq, to, 0, FLAG_CAPTURE);
              }
            } else if (to === state.ep) {
              buf[idx++] = encodeMove(sq, to, 0, FLAG_EP | FLAG_CAPTURE);
            }
          }

          const fwd = (nr << 3) | c;
          if (b[fwd] === 0) {
            if (nr === promoRow) {
              buf[idx++] = encodeMove(sq, fwd, WQ, 0);
              if (!capturesOnly) {
                buf[idx++] = encodeMove(sq, fwd, WR, 0);
                buf[idx++] = encodeMove(sq, fwd, WB, 0);
                buf[idx++] = encodeMove(sq, fwd, WN, 0);
              }
            } else if (!capturesOnly) {
              buf[idx++] = encodeMove(sq, fwd, 0, 0);
              if (r === startRow) {
                const dbl = ((r + dir * 2) << 3) | c;
                if (b[dbl] === 0) buf[idx++] = encodeMove(sq, dbl, 0, 0);
              }
            }
          }
        }
      } else if (type === WN) {
        for (let i = 0; i < 8; i++) {
          const nr = r + KNIGHT_DR[i];
          const nc = c + KNIGHT_DC[i];
          if ((nr | nc) < 0 || nr > 7 || nc > 7) continue;
          const to = (nr << 3) | nc;
          const t = b[to];
          if (t === 0) {
            if (!capturesOnly) buf[idx++] = encodeMove(sq, to, 0, 0);
          } else if ((t > 0 ? 1 : -1) === -turn) {
            buf[idx++] = encodeMove(sq, to, 0, FLAG_CAPTURE);
          }
        }
      } else if (type === WK) {
        for (let i = 0; i < 8; i++) {
          const nr = r + KING_DR[i];
          const nc = c + KING_DC[i];
          if ((nr | nc) < 0 || nr > 7 || nc > 7) continue;
          const to = (nr << 3) | nc;
          const t = b[to];
          if (t === 0) {
            if (!capturesOnly) buf[idx++] = encodeMove(sq, to, 0, 0);
          } else if ((t > 0 ? 1 : -1) === -turn) {
            buf[idx++] = encodeMove(sq, to, 0, FLAG_CAPTURE);
          }
        }
        if (!capturesOnly) {
          if (turn === 1 && sq === 60) {
            if ((state.castling & 1) && b[61] === 0 && b[62] === 0 && b[63] === WR) {
              if (!isSquareAttacked(state, 60, -1) && !isSquareAttacked(state, 61, -1) && !isSquareAttacked(state, 62, -1)) {
                buf[idx++] = encodeMove(60, 62, 0, FLAG_CASTLE);
              }
            }
            if ((state.castling & 2) && b[59] === 0 && b[58] === 0 && b[57] === 0 && b[56] === WR) {
              if (!isSquareAttacked(state, 60, -1) && !isSquareAttacked(state, 59, -1) && !isSquareAttacked(state, 58, -1)) {
                buf[idx++] = encodeMove(60, 58, 0, FLAG_CASTLE);
              }
            }
          } else if (turn === -1 && sq === 4) {
            if ((state.castling & 4) && b[5] === 0 && b[6] === 0 && b[7] === BR) {
              if (!isSquareAttacked(state, 4, 1) && !isSquareAttacked(state, 5, 1) && !isSquareAttacked(state, 6, 1)) {
                buf[idx++] = encodeMove(4, 6, 0, FLAG_CASTLE);
              }
            }
            if ((state.castling & 8) && b[3] === 0 && b[2] === 0 && b[1] === 0 && b[0] === BR) {
              if (!isSquareAttacked(state, 4, 1) && !isSquareAttacked(state, 3, 1) && !isSquareAttacked(state, 2, 1)) {
                buf[idx++] = encodeMove(4, 2, 0, FLAG_CASTLE);
              }
            }
          }
        }
      } else {
        if (type === WB || type === WQ) {
          for (let d = 0; d < 4; d++) {
            let nr = r + DIAG_DR[d], nc = c + DIAG_DC[d];
            while (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
              const to = (nr << 3) | nc;
              const t = b[to];
              if (t === 0) {
                if (!capturesOnly) buf[idx++] = encodeMove(sq, to, 0, 0);
              } else {
                if ((t > 0 ? 1 : -1) === -turn) buf[idx++] = encodeMove(sq, to, 0, FLAG_CAPTURE);
                break;
              }
              nr += DIAG_DR[d];
              nc += DIAG_DC[d];
            }
          }
        }
        if (type === WR || type === WQ) {
          for (let d = 0; d < 4; d++) {
            let nr = r + ORTHO_DR[d], nc = c + ORTHO_DC[d];
            while (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
              const to = (nr << 3) | nc;
              const t = b[to];
              if (t === 0) {
                if (!capturesOnly) buf[idx++] = encodeMove(sq, to, 0, 0);
              } else {
                if ((t > 0 ? 1 : -1) === -turn) buf[idx++] = encodeMove(sq, to, 0, FLAG_CAPTURE);
                break;
              }
              nr += ORTHO_DR[d];
              nc += ORTHO_DC[d];
            }
          }
        }
      }
    }
    return idx;
  }

  function makeMove(state, move, undo) {
    const b = state.board;
    const from = move & 63;
    const to = (move >> 6) & 63;
    const promo = (move >> 12) & 7;
    const flags = (move >> 15) & 7;
    const turn = state.turn;

    const piece = b[from];
    let cap = b[to];

    undo.movedPiece = piece;
    undo.cap = cap;
    undo.castling = state.castling;
    undo.ep = state.ep;
    undo.halfmove = state.halfmove;
    undo.hLo = state.hLo;
    undo.hHi = state.hHi;

    let lo = state.hLo;
    let hi = state.hHi;

    let zIdx = (piece + 6) * 64 + from;
    lo ^= zPieceLo[zIdx]; hi ^= zPieceHi[zIdx];
    lo ^= zCastleLo[state.castling]; hi ^= zCastleHi[state.castling];
    const oldEpIdx = state.ep === -1 ? 64 : state.ep;
    lo ^= zEpLo[oldEpIdx]; hi ^= zEpHi[oldEpIdx];

    b[from] = 0;

    if (flags & FLAG_EP) {
      const epSq = turn === 1 ? to + 8 : to - 8;
      cap = b[epSq];
      undo.cap = cap;
      zIdx = (cap + 6) * 64 + epSq;
      lo ^= zPieceLo[zIdx]; hi ^= zPieceHi[zIdx];
      b[epSq] = 0;
    } else if (cap !== 0) {
      zIdx = (cap + 6) * 64 + to;
      lo ^= zPieceLo[zIdx]; hi ^= zPieceHi[zIdx];
    }

    const placed = promo ? turn * promo : piece;
    b[to] = placed;
    zIdx = (placed + 6) * 64 + to;
    lo ^= zPieceLo[zIdx]; hi ^= zPieceHi[zIdx];

    if (piece === WK) state.wKing = to;
    else if (piece === BK) state.bKing = to;

    if (flags & FLAG_CASTLE) {
      let rFrom = 0, rTo = 0;
      if (to === 62) { rFrom = 63; rTo = 61; }
      else if (to === 58) { rFrom = 56; rTo = 59; }
      else if (to === 6) { rFrom = 7; rTo = 5; }
      else if (to === 2) { rFrom = 0; rTo = 3; }
      const rook = b[rFrom];
      b[rFrom] = 0;
      b[rTo] = rook;
      zIdx = (rook + 6) * 64 + rFrom;
      lo ^= zPieceLo[zIdx]; hi ^= zPieceHi[zIdx];
      zIdx = (rook + 6) * 64 + rTo;
      lo ^= zPieceLo[zIdx]; hi ^= zPieceHi[zIdx];
    }

    state.castling &= CASTLE_MASK[from] & CASTLE_MASK[to];
    if ((piece === WP || piece === BP) && Math.abs(to - from) === 16) {
      state.ep = (from + to) >> 1;
    } else {
      state.ep = -1;
    }

    if (piece === WP || piece === BP || cap !== 0) state.halfmove = 0;
    else state.halfmove++;

    if (turn === -1) state.fullmove++;
    state.turn = -turn;

    lo ^= zCastleLo[state.castling]; hi ^= zCastleHi[state.castling];
    const newEpIdx = state.ep === -1 ? 64 : state.ep;
    lo ^= zEpLo[newEpIdx]; hi ^= zEpHi[newEpIdx];
    lo ^= zSideLo; hi ^= zSideHi;

    state.hLo = lo >>> 0;
    state.hHi = hi >>> 0;
  }

  function unmakeMove(state, move, undo) {
    const b = state.board;
    const from = move & 63;
    const to = (move >> 6) & 63;
    const flags = (move >> 15) & 7;

    state.turn = -state.turn;
    const turn = state.turn;
    if (turn === -1) state.fullmove--;

    state.castling = undo.castling;
    state.ep = undo.ep;
    state.halfmove = undo.halfmove;
    state.hLo = undo.hLo;
    state.hHi = undo.hHi;

    const piece = undo.movedPiece;
    b[from] = piece;
    if (piece === WK) state.wKing = from;
    else if (piece === BK) state.bKing = from;

    if (flags & FLAG_EP) {
      b[to] = 0;
      const epSq = turn === 1 ? to + 8 : to - 8;
      b[epSq] = undo.cap;
    } else {
      b[to] = undo.cap;
    }

    if (flags & FLAG_CASTLE) {
      let rFrom = 0, rTo = 0;
      if (to === 62) { rFrom = 63; rTo = 61; }
      else if (to === 58) { rFrom = 56; rTo = 59; }
      else if (to === 6) { rFrom = 7; rTo = 5; }
      else if (to === 2) { rFrom = 0; rTo = 3; }
      b[rFrom] = b[rTo];
      b[rTo] = 0;
    }
  }

  function makeNullMove(state, undo) {
    undo.ep = state.ep;
    undo.hLo = state.hLo;
    undo.hHi = state.hHi;
    let lo = state.hLo, hi = state.hHi;
    const oldEpIdx = state.ep === -1 ? 64 : state.ep;
    lo ^= zEpLo[oldEpIdx]; hi ^= zEpHi[oldEpIdx];
    state.ep = -1;
    lo ^= zEpLo[64]; hi ^= zEpHi[64];
    lo ^= zSideLo; hi ^= zSideHi;
    state.turn = -state.turn;
    state.hLo = lo >>> 0;
    state.hHi = hi >>> 0;
  }

  function unmakeNullMove(state, undo) {
    state.turn = -state.turn;
    state.ep = undo.ep;
    state.hLo = undo.hLo;
    state.hHi = undo.hHi;
  }

  function generateLegalMoves(state) {
    const tmp = new Int32Array(256);
    const count = generatePseudoMoves(state, tmp, 0, false);
    const legal = [];
    const undo = {};
    const side = state.turn;
    for (let i = 0; i < count; i++) {
      const m = tmp[i];
      makeMove(state, m, undo);
      if (!inCheck(state, side)) legal.push(m);
      unmakeMove(state, m, undo);
    }
    return legal;
  }

  function isInsufficientMaterial(state) {
    const b = state.board;
    let wMinors = 0, bMinors = 0, wBishColor = -1, bBishColor = -1;
    for (let sq = 0; sq < 64; sq++) {
      const p = b[sq];
      if (p === 0 || p === WK || p === BK) continue;
      const abs = p > 0 ? p : -p;
      if (abs === WP || abs === WR || abs === WQ) return false;
      if (p > 0) {
        wMinors++;
        if (abs === WB) wBishColor = ((sq >> 3) + (sq & 7)) & 1;
      } else {
        bMinors++;
        if (abs === WB) bBishColor = ((sq >> 3) + (sq & 7)) & 1;
      }
    }
    if (wMinors === 0 && bMinors === 0) return true;
    if (wMinors + bMinors === 1) return true;
    if (wMinors === 1 && bMinors === 1 && wBishColor !== -1 && wBishColor === bBishColor) return true;
    return false;
  }

  return {
    EMPTY, WP, WN, WB, WR, WQ, WK, BP, BN, BB, BR, BQ, BK,
    FLAG_EP, FLAG_CASTLE, FLAG_CAPTURE,
    encodeMove, sqToAlgebraic, moveToUci,
    createInitialState, cloneState,
    isSquareAttacked, inCheck, generatePseudoMoves, generateLegalMoves,
    makeMove, unmakeMove, makeNullMove, unmakeNullMove,
    isInsufficientMaterial
  };
}

/* ============================================================================
   2. IMPOSSIBLE MATH & PHYSICS AI WEB WORKER
   ============================================================================ */
function chessWorkerMain() {
  const C = createChessCore();

  const MG_VAL = [0, 82, 337, 365, 477, 1025, 0];
  const EG_VAL = [0, 94, 281, 297, 512, 936, 0];
  const PHASE_W = [0, 0, 1, 1, 2, 4, 0];
  const SEE_VAL = [0, 100, 320, 330, 500, 900, 20000];

  const MG_PST = [
    null,
    [
       0,  0,  0,  0,  0,  0,  0,  0,
      98,134, 61, 95, 68,126, 34,-11,
      -6,  7, 26, 31, 65, 56, 25,-20,
     -14, 13,  6, 21, 23, 12, 17,-23,
     -27, -2, -5, 12, 17,  6, 10,-25,
     -26, -4, -4,-10,  3,  3, 33,-12,
     -35, -1,-20,-23,-15, 24, 38,-22,
       0,  0,  0,  0,  0,  0,  0,  0
    ],
    [
    -167,-89,-34,-49, 61,-97,-15,-107,
     -73,-41, 72, 36, 23, 62,  7, -17,
     -47, 60, 37, 65, 84,129, 73,  44,
      -9, 17, 19, 53, 37, 69, 18,  22,
     -13,  4, 16, 13, 28, 19, 21,  -8,
     -23, -9, 12, 10, 19, 17, 25, -16,
     -29,-53,-12, -3, -1, 18,-14, -19,
    -105,-21,-58,-33,-17,-28,-19, -23
    ],
    [
     -29,  4,-82,-37,-25,-42,  7,  -8,
     -26, 16,-18,-13, 30, 59, 18, -47,
     -16, 37, 43, 40, 35, 50, 37,  -2,
      -4,  5, 19, 50, 37, 37,  7,  -2,
      -6, 13, 13, 26, 34, 12, 10,   4,
       0, 15, 15, 15, 14, 27, 18,  10,
       4, 15, 16,  0,  7, 21, 33,   1,
     -33, -3,-14,-21,-13,-12,-39, -21
    ],
    [
      32, 42, 32, 51, 63,  9, 31,  43,
      27, 32, 58, 62, 80, 67, 26,  44,
      -5, 19, 26, 36, 17, 45, 61,  16,
     -24,-11,  7, 26, 24, 35, -8, -20,
     -36,-26,-12, -1,  9, -7,  6, -23,
     -45,-25,-16,-17,  3,  0, -5, -33,
     -44,-16,-20, -9, -1, 11, -6, -71,
     -19,-13,  1, 17, 16,  7,-37, -26
    ],
    [
     -28,  0, 29, 12, 59, 44, 43,  45,
     -24,-39, -5,  1,-16, 57, 28,  54,
     -13,-17,  7,  8, 29, 56, 47,  57,
     -27,-27,-16,-16, -1, 17, -2,   1,
      -9,-26, -9,-10, -2, -4,  3,  -3,
     -14,  2,-11, -2, -5,  2, 14,   5,
     -35, -8, 11,  2,  8, 15, -3,   1,
      -1,-18, -9, 10,-15,-25,-31, -50
    ],
    [
     -65, 23, 16,-15,-56,-34,  2,  13,
      29, -1,-20, -7, -8, -4,-38, -29,
      -9, 24,  2,-16,-20,  6, 22, -22,
     -17,-20,-12,-27,-30,-25,-14, -36,
     -49, -1,-27,-39,-46,-44,-33, -51,
     -14,-14,-22,-46,-44,-30,-15, -27,
       1,  7, -8,-64,-43,-16,  9,   8,
     -15, 36, 12,-54,  8,-28, 24,  14
    ]
  ];

  const EG_PST = [
    null,
    [
       0,  0,  0,  0,  0,  0,  0,  0,
     178,173,158,134,147,132,165,187,
      94,100, 85, 67, 56, 53, 82, 84,
      32, 24, 13,  5, -2,  4, 17, 17,
      13,  9, -3, -7, -7, -8,  3, -1,
       4,  7, -6,  1,  0, -5, -1, -8,
      13,  8,  8, 10, 13,  0,  2, -7,
       0,  0,  0,  0,  0,  0,  0,  0
    ],
    [
     -58,-38,-13,-28,-31,-27,-63,-99,
     -25, -8,-25, -2, -9,-25,-24,-52,
     -24,-20, 10,  9, -1, -9,-19,-41,
     -17,  3, 22, 22, 22, 11,  8,-18,
     -18, -6, 16, 25, 16, 17,  4,-18,
     -23, -3, -1, 15, 10, -3,-20,-22,
     -42,-20,-10, -5, -2,-20,-23,-44,
     -29,-51,-23,-15,-22,-18,-50,-64
    ],
    [
     -14,-21,-11, -8, -7, -9,-17,-24,
      -8, -4,  7,-12, -3,-13, -4,-14,
       2, -8,  0, -1, -2,  6,  0,  4,
      -3,  9, 12,  9, 14, 10,  3,  2,
      -6,  3, 13, 19,  7, 10, -3, -9,
     -12, -3,  8, 10, 13,  3, -7,-15,
     -14,-18, -7, -1,  4, -9,-15,-27,
     -23, -9,-23, -5, -9,-16, -5,-17
    ],
    [
      13, 10, 18, 15, 12, 12,  8,  5,
      11, 13, 13, 11, -3,  3,  8,  3,
       7,  7,  7,  5,  4, -3, -5, -3,
       4,  3, 13,  1,  2,  1, -1,  2,
       3,  5,  8,  4, -5, -6, -8,-11,
      -4,  0, -5, -1, -7,-12, -8,-16,
      -6, -6,  0,  2, -9, -9,-11, -3,
      -9,  2,  3, -1, -5,-13,  4,-20
    ],
    [
      -9, 22, 22, 27, 27, 19, 10, 20,
     -17, 20, 32, 41, 58, 25, 30,  0,
     -20,  6,  9, 49, 47, 35, 19,  9,
       3, 22, 24, 45, 57, 40, 57, 36,
     -18, 28, 19, 47, 31, 34, 39, 23,
     -16,-27, 15,  6,  9, 17, 10,  5,
     -22,-23,-30,-16,-16,-23,-36,-32,
     -33,-28,-22,-43, -5,-32,-20,-41
    ],
    [
     -74,-35,-18,-18,-11, 15,  4,-17,
     -12, 17, 14, 17, 17, 38, 23, 11,
      10, 17, 23, 15, 20, 45, 44, 13,
      -8, 22, 24, 27, 26, 33, 26,  3,
     -18, -4, 21, 24, 27, 23,  9,-11,
     -19, -3, 11, 21, 23, 16,  7, -9,
     -27,-11,  4, 13, 14,  4, -5,-17,
     -53,-34,-21,-11,-28,-14,-24,-43
    ]
  ];

  const CENTER_DIST = new Uint8Array(64);
  for (let sq = 0; sq < 64; sq++) {
    const r = sq >> 3, c = sq & 7;
    CENTER_DIST[sq] = Math.max(3 - r, r - 4) + Math.max(3 - c, c - 4);
  }

  const OPENING_BOOK = {
    '': ['e2e4', 'd2d4'],
    'e2e4': ['c7c5', 'e7e5'],
    'e2e4 c7c5': ['g1f3'],
    'e2e4 c7c5 g1f3': ['d7d6', 'b8c6'],
    'e2e4 c7c5 g1f3 d7d6': ['d2d4'],
    'e2e4 c7c5 g1f3 d7d6 d2d4': ['c5d4'],
    'e2e4 c7c5 g1f3 d7d6 d2d4 c5d4': ['f3d4'],
    'e2e4 c7c5 g1f3 d7d6 d2d4 c5d4 f3d4': ['g8f6'],
    'e2e4 c7c5 g1f3 d7d6 d2d4 c5d4 f3d4 g8f6': ['b1c3'],
    'e2e4 c7c5 g1f3 d7d6 d2d4 c5d4 f3d4 g8f6 b1c3': ['a7a6'],
    'e2e4 e7e5': ['g1f3'],
    'e2e4 e7e5 g1f3': ['b8c6'],
    'e2e4 e7e5 g1f3 b8c6': ['f1b5'],
    'e2e4 e7e5 g1f3 b8c6 f1b5': ['a7a6'],
    'e2e4 e7e5 g1f3 b8c6 f1b5 a7a6': ['b5a4'],
    'e2e4 e7e5 g1f3 b8c6 f1b5 a7a6 b5a4': ['g8f6'],
    'd2d4': ['g8f6', 'd7d5'],
    'd2d4 d7d5': ['c2c4'],
    'd2d4 d7d5 c2c4': ['e7e6'],
    'd2d4 d7d5 c2c4 e7e6': ['b1c3'],
    'd2d4 g8f6': ['c2c4'],
    'd2d4 g8f6 c2c4': ['e7e6', 'g7g6'],
    'c2c4': ['e7e5'],
    'g1f3': ['d7d5']
  };

  const TT_SIZE = 1 << 19;
  const TT_MASK = TT_SIZE - 1;
  const ttKeyHi = new Uint32Array(TT_SIZE);
  const ttKeyLo = new Uint32Array(TT_SIZE);
  const ttMove = new Int32Array(TT_SIZE);
  const ttScore = new Int16Array(TT_SIZE);
  const ttDepth = new Int8Array(TT_SIZE);
  const ttFlag = new Uint8Array(TT_SIZE);
  const TT_EXACT = 1, TT_LOWER = 2, TT_UPPER = 3;

  const MAX_PLY = 64;
  const MOVE_BUF = new Int32Array(MAX_PLY * 256);
  const SCORE_BUF = new Int32Array(MAX_PLY * 256);
  const UNDO_STACK = Array.from({ length: MAX_PLY + 4 }, () => ({}));
  const KILLERS = new Int32Array(MAX_PLY * 2);
  const HISTORY = new Int32Array(2 * 64 * 64);
  const COUNTERMOVE = new Int32Array(64 * 64);
  const HIST_MAX = 16384;

  // Logarithmic Late Move Reductions: R(d, m) = floor(0.77 + ln(d)*ln(m)/2.36)
  const LMR_TABLE = [];
  for (let d = 0; d < 64; d++) {
    LMR_TABLE[d] = new Uint8Array(64);
    for (let m = 0; m < 64; m++) {
      if (d > 0 && m > 0) {
        LMR_TABLE[d][m] = Math.floor(0.77 + (Math.log(d) * Math.log(m)) / 2.36);
      }
    }
  }

  let nodes = 0;
  let startTime = 0;
  let timeLimit = 3800;
  let stopSearch = false;
  let repHistory = new Map();

  const wPawnFiles = new Uint8Array(8);
  const bPawnFiles = new Uint8Array(8);
  const wPawnMinRow = new Uint8Array(8);
  const bPawnMaxRow = new Uint8Array(8);

  function evaluate(state) {
    const b = state.board;
    let mgW = 0, egW = 0, mgB = 0, egB = 0;
    let phase = 0;
    let wBishops = 0, bBishops = 0;

    wPawnFiles.fill(0);
    bPawnFiles.fill(0);
    wPawnMinRow.fill(8);
    bPawnMaxRow.fill(0);

    const wKr = state.wKing >> 3, wKc = state.wKing & 7;
    const bKr = state.bKing >> 3, bKc = state.bKing & 7;

    let attackOnWhite = 0, attackOnBlack = 0;
    let wFieldPot = 0, bFieldPot = 0;
    const ATK_W = [0, 0, 20, 20, 40, 80, 0];

    for (let sq = 0; sq < 64; sq++) {
      const p = b[sq];
      if (p === 0) continue;
      const r = sq >> 3, c = sq & 7;

      if (p > 0) {
        mgW += MG_VAL[p] + MG_PST[p][sq];
        egW += EG_VAL[p] + EG_PST[p][sq];
        phase += PHASE_W[p];
        if (p === 1) {
          wPawnFiles[c]++;
          if (r < wPawnMinRow[c]) wPawnMinRow[c] = r;
        } else if (p === 3) wBishops++;
        if (p >= 2 && p <= 5) {
          const dInf = Math.max(Math.abs(r - bKr), Math.abs(c - bKc));
          bFieldPot += ATK_W[p] / (1 + dInf);
          if (dInf <= 2) attackOnBlack += ATK_W[p];
        }
      } else {
        const t = -p;
        const flipSq = sq ^ 56;
        mgB += MG_VAL[t] + MG_PST[t][flipSq];
        egB += EG_VAL[t] + EG_PST[t][flipSq];
        phase += PHASE_W[t];
        if (t === 1) {
          bPawnFiles[c]++;
          if (r > bPawnMaxRow[c]) bPawnMaxRow[c] = r;
        } else if (t === 3) bBishops++;
        if (t >= 2 && t <= 5) {
          const dInf = Math.max(Math.abs(r - wKr), Math.abs(c - wKc));
          wFieldPot += ATK_W[t] / (1 + dInf);
          if (dInf <= 2) attackOnWhite += ATK_W[t];
        }
      }
    }

    if (wBishops >= 2) { mgW += 34; egW += 52; }
    if (bBishops >= 2) { mgB += 34; egB += 52; }

    // King Threat Potential Field Energy
    mgW += Math.min(350, bFieldPot + 0.008 * attackOnBlack * attackOnBlack);
    mgB += Math.min(350, wFieldPot + 0.008 * attackOnWhite * attackOnWhite);

    for (let f = 0; f < 8; f++) {
      const wc = wPawnFiles[f], bc = bPawnFiles[f];
      if (wc > 1) { mgW -= 14 * (wc - 1); egW -= 22 * (wc - 1); }
      if (bc > 1) { mgB -= 14 * (bc - 1); egB -= 22 * (bc - 1); }

      const wLeft = f > 0 ? wPawnFiles[f - 1] : 0;
      const wRight = f < 7 ? wPawnFiles[f + 1] : 0;
      if (wc > 0 && wLeft === 0 && wRight === 0) { mgW -= 14; egW -= 18; }

      const bLeft = f > 0 ? bPawnFiles[f - 1] : 0;
      const bRight = f < 7 ? bPawnFiles[f + 1] : 0;
      if (bc > 0 && bLeft === 0 && bRight === 0) { mgB -= 14; egB -= 18; }

      if (wc > 0) {
        const wr = wPawnMinRow[f];
        const bBlock = (bPawnFiles[f] > 0 && bPawnMaxRow[f] < wr) ||
          (f > 0 && bPawnFiles[f - 1] > 0 && bPawnMaxRow[f - 1] < wr) ||
          (f < 7 && bPawnFiles[f + 1] > 0 && bPawnMaxRow[f + 1] < wr);
        if (!bBlock) {
          const adv = 7 - wr;
          mgW += adv * adv * 4;
          egW += adv * adv * 11;
        }
      }
      if (bc > 0) {
        const br = bPawnMaxRow[f];
        const wBlock = (wPawnFiles[f] > 0 && wPawnMinRow[f] > br) ||
          (f > 0 && wPawnFiles[f - 1] > 0 && wPawnMinRow[f - 1] > br) ||
          (f < 7 && wPawnFiles[f + 1] > 0 && wPawnMinRow[f + 1] > br);
        if (!wBlock) {
          const adv = br;
          mgB += adv * adv * 4;
          egB += adv * adv * 11;
        }
      }
    }

    for (let sq = 0; sq < 64; sq++) {
      const p = b[sq];
      if (p === 4) {
        const f = sq & 7, r = sq >> 3;
        if (wPawnFiles[f] === 0) {
          const bonus = bPawnFiles[f] === 0 ? 26 : 13;
          mgW += bonus; egW += bonus * 0.7;
        }
        if (r === 1) { mgW += 22; egW += 36; }
      } else if (p === -4) {
        const f = sq & 7, r = sq >> 3;
        if (bPawnFiles[f] === 0) {
          const bonus = wPawnFiles[f] === 0 ? 26 : 13;
          mgB += bonus; egB += bonus * 0.7;
        }
        if (r === 6) { mgB += 22; egB += 36; }
      }
    }

    const phi = (phase > 24 ? 24 : phase) / 24;
    let score = phi * (mgW - mgB) + (1 - phi) * (egW - egB);

    // Endgame Mop-Up Metric (Manhattan L1)
    if (phi < 0.25) {
      const kingDist = Math.abs(wKr - bKr) + Math.abs(wKc - bKc);
      if (score > 250) {
        score += (4.7 * CENTER_DIST[state.bKing] + 1.6 * (14 - kingDist)) * (1 - phi * 4);
      } else if (score < -250) {
        score -= (4.7 * CENTER_DIST[state.wKing] + 1.6 * (14 - kingDist)) * (1 - phi * 4);
      }
    }

    score += state.turn * 14;
    return Math.round(score * state.turn);
  }

  function updateHistory(colorIdx, from, to, bonus) {
    const idx = (colorIdx << 12) | (from << 6) | to;
    const clamped = Math.max(-400, Math.min(400, bonus));
    HISTORY[idx] += clamped - Math.trunc((HISTORY[idx] * Math.abs(clamped)) / HIST_MAX);
  }

  function scoreMoves(state, offset, count, ply, ttBest, prevMove) {
    const b = state.board;
    const colorIdx = state.turn === 1 ? 0 : 1;
    const k1 = KILLERS[ply * 2];
    const k2 = KILLERS[ply * 2 + 1];
    const cm = prevMove ? COUNTERMOVE[((prevMove & 63) << 6) | ((prevMove >> 6) & 63)] : 0;

    for (let i = offset; i < count; i++) {
      const m = MOVE_BUF[i];
      if (m === ttBest) { SCORE_BUF[i] = 2000000; continue; }
      const from = m & 63;
      const to = (m >> 6) & 63;
      const promo = (m >> 12) & 7;
      const flags = (m >> 15) & 7;

      if (flags & C.FLAG_CAPTURE) {
        const victim = (flags & C.FLAG_EP) ? 1 : Math.abs(b[to]);
        const attacker = Math.abs(b[from]);
        SCORE_BUF[i] = 1000000 + SEE_VAL[victim] * 10 - SEE_VAL[attacker];
      } else if (promo) {
        SCORE_BUF[i] = 900000 + SEE_VAL[promo];
      } else if (m === k1) {
        SCORE_BUF[i] = 800000;
      } else if (m === k2) {
        SCORE_BUF[i] = 750000;
      } else if (m === cm) {
        SCORE_BUF[i] = 700000;
      } else {
        SCORE_BUF[i] = HISTORY[(colorIdx << 12) | (from << 6) | to];
      }
    }
  }

  function pickNextMove(offset, count, idx) {
    let bestI = idx, bestS = SCORE_BUF[idx];
    for (let i = idx + 1; i < count; i++) {
      if (SCORE_BUF[i] > bestS) { bestS = SCORE_BUF[i]; bestI = i; }
    }
    if (bestI !== idx) {
      const tm = MOVE_BUF[idx]; MOVE_BUF[idx] = MOVE_BUF[bestI]; MOVE_BUF[bestI] = tm;
      const ts = SCORE_BUF[idx]; SCORE_BUF[idx] = SCORE_BUF[bestI]; SCORE_BUF[bestI] = ts;
    }
    return MOVE_BUF[idx];
  }

  function hasNonPawnMaterial(state) {
    const b = state.board, t = state.turn;
    for (let sq = 0; sq < 64; sq++) {
      const p = b[sq] * t;
      if (p >= 2 && p <= 5) return true;
    }
    return false;
  }

  function qsearch(state, alpha, beta, ply) {
    nodes++;
    if ((nodes & 2047) === 0 && performance.now() - startTime >= timeLimit) {
      stopSearch = true;
      return 0;
    }
    if (ply >= MAX_PLY - 1) return evaluate(state);

    const standPat = evaluate(state);
    if (standPat >= beta) return beta;
    if (standPat > alpha) alpha = standPat;

    const offset = ply * 256;
    const end = C.generatePseudoMoves(state, MOVE_BUF, offset, true);
    scoreMoves(state, offset, end, ply, 0, 0);

    const undo = UNDO_STACK[ply];
    const side = state.turn;

    for (let i = offset; i < end; i++) {
      const m = pickNextMove(offset, end, i);
      const to = (m >> 6) & 63;
      const promo = (m >> 12) & 7;
      const flags = (m >> 15) & 7;
      const victim = (flags & C.FLAG_EP) ? 1 : Math.abs(state.board[to]);

      if (!promo && standPat + SEE_VAL[victim] + 220 < alpha) continue;

      C.makeMove(state, m, undo);
      if (C.inCheck(state, side)) { C.unmakeMove(state, m, undo); continue; }
      const score = -qsearch(state, -beta, -alpha, ply + 1);
      C.unmakeMove(state, m, undo);

      if (stopSearch) return 0;
      if (score >= beta) return beta;
      if (score > alpha) alpha = score;
    }
    return alpha;
  }

  function search(state, depth, alpha, beta, ply, allowNull, prevMove) {
    if (ply >= MAX_PLY - 1) return evaluate(state);

    const isRoot = ply === 0;
    const isPV = (beta - alpha) > 1;

    if (!isRoot) {
      if (state.halfmove >= 100 || C.isInsufficientMaterial(state)) return 0;
      const key = state.hHi * 4294967296 + state.hLo;
      if ((repHistory.get(key) || 0) >= 2) return 0;
    }

    const inChk = C.inCheck(state, state.turn);
    if (inChk && depth < 14) depth++;
    if (depth <= 0) return qsearch(state, alpha, beta, ply);

    nodes++;
    if ((nodes & 2047) === 0 && performance.now() - startTime >= timeLimit) {
      stopSearch = true;
      return 0;
    }

    const ttIdx = state.hLo & TT_MASK;
    let ttBest = 0;
    if (ttKeyLo[ttIdx] === state.hLo && ttKeyHi[ttIdx] === state.hHi && ttFlag[ttIdx] !== 0) {
      ttBest = ttMove[ttIdx];
      if (!isPV && ttDepth[ttIdx] >= depth) {
        let s = ttScore[ttIdx];
        if (s > 28000) s -= ply;
        else if (s < -28000) s += ply;
        const fl = ttFlag[ttIdx];
        if (fl === TT_EXACT) return s;
        if (fl === TT_LOWER && s >= beta) return s;
        if (fl === TT_UPPER && s <= alpha) return s;
      }
    }

    const staticEval = inChk ? -30000 : evaluate(state);

    // Reverse Futility Pruning
    if (!isPV && !inChk && depth <= 3 && Math.abs(beta) < 28000) {
      if (staticEval - 120 * depth >= beta) return staticEval;
    }

    // Dynamic Null-Move Pruning
    if (allowNull && !isPV && !inChk && depth >= 3 && staticEval >= beta && hasNonPawnMaterial(state)) {
      const R = 3 + Math.floor(depth / 6) + Math.min(3, Math.floor((staticEval - beta) / 200));
      const undoNull = UNDO_STACK[ply];
      C.makeNullMove(state, undoNull);
      const nullScore = -search(state, depth - 1 - R, -beta, -beta + 1, ply + 1, false, 0);
      C.unmakeNullMove(state, undoNull);
      if (stopSearch) return 0;
      if (nullScore >= beta) return beta;
    }

    const offset = ply * 256;
    const end = C.generatePseudoMoves(state, MOVE_BUF, offset, false);
    scoreMoves(state, offset, end, ply, ttBest, prevMove);

    const origAlpha = alpha;
    const side = state.turn;
    const colorIdx = side === 1 ? 0 : 1;
    const undo = UNDO_STACK[ply];
    let bestMove = 0;
    let bestScore = -32000;
    let legalCount = 0;

    const curKey = state.hHi * 4294967296 + state.hLo;
    repHistory.set(curKey, (repHistory.get(curKey) || 0) + 1);

    for (let i = offset; i < end; i++) {
      const m = pickNextMove(offset, end, i);
      const flags = (m >> 15) & 7;
      const promo = (m >> 12) & 7;
      const isQuiet = !(flags & C.FLAG_CAPTURE) && promo === 0;

      if (!isPV && !inChk && isQuiet && depth <= 2 && legalCount > 3 && staticEval + 140 * depth <= alpha) {
        continue;
      }

      C.makeMove(state, m, undo);
      if (C.inCheck(state, side)) { C.unmakeMove(state, m, undo); continue; }
      legalCount++;

      let score;
      const givesCheck = C.inCheck(state, state.turn);

      if (legalCount === 1) {
        score = -search(state, depth - 1, -beta, -alpha, ply + 1, true, m);
      } else {
        let reduction = 0;
        if (depth >= 3 && legalCount >= 4 && isQuiet && !inChk && !givesCheck) {
          reduction = LMR_TABLE[Math.min(63, depth)][Math.min(63, legalCount)];
          if (isPV) reduction = Math.max(0, reduction - 1);
          reduction = Math.min(depth - 2, reduction);
        }

        score = -search(state, depth - 1 - reduction, -alpha - 1, -alpha, ply + 1, true, m);
        if (score > alpha && reduction > 0) {
          score = -search(state, depth - 1, -alpha - 1, -alpha, ply + 1, true, m);
        }
        if (score > alpha && score < beta) {
          score = -search(state, depth - 1, -beta, -alpha, ply + 1, true, m);
        }
      }

      C.unmakeMove(state, m, undo);
      if (stopSearch) {
        repHistory.set(curKey, repHistory.get(curKey) - 1);
        return 0;
      }

      if (score > bestScore) {
        bestScore = score;
        bestMove = m;
        if (score > alpha) {
          alpha = score;
          if (alpha >= beta) {
            if (isQuiet) {
              if (KILLERS[ply * 2] !== m) {
                KILLERS[ply * 2 + 1] = KILLERS[ply * 2];
                KILLERS[ply * 2] = m;
              }
              updateHistory(colorIdx, m & 63, (m >> 6) & 63, depth * depth);
              if (prevMove) {
                COUNTERMOVE[((prevMove & 63) << 6) | ((prevMove >> 6) & 63)] = m;
              }
            }
            break;
          }
        }
      } else if (isQuiet) {
        updateHistory(colorIdx, m & 63, (m >> 6) & 63, -depth);
      }
    }

    repHistory.set(curKey, repHistory.get(curKey) - 1);
    if (legalCount === 0) return inChk ? -30000 + ply : 0;

    let storeScore = bestScore;
    if (storeScore > 28000) storeScore += ply;
    else if (storeScore < -28000) storeScore -= ply;

    ttKeyLo[ttIdx] = state.hLo;
    ttKeyHi[ttIdx] = state.hHi;
    ttMove[ttIdx] = bestMove;
    ttScore[ttIdx] = storeScore;
    ttDepth[ttIdx] = depth;
    ttFlag[ttIdx] = bestScore <= origAlpha ? TT_UPPER : (bestScore >= beta ? TT_LOWER : TT_EXACT);

    return bestScore;
  }

  function findBestMove(state, uciHistory, historyHashes) {
    const legalMoves = C.generateLegalMoves(state);
    if (legalMoves.length === 0) return null;
    if (legalMoves.length === 1) return legalMoves[0];

    // Master Opening Book
    const seq = uciHistory.join(' ');
    const bookChoices = OPENING_BOOK[seq];
    if (bookChoices && bookChoices.length > 0) {
      const found = legalMoves.find(m => C.moveToUci(m) === bookChoices[0]);
      if (found) return found;
    }

    repHistory = new Map();
    for (let i = 0; i < historyHashes.length; i++) {
      const k = historyHashes[i];
      repHistory.set(k, (repHistory.get(k) || 0) + 1);
    }
    KILLERS.fill(0);
    for (let i = 0; i < HISTORY.length; i++) HISTORY[i] >>= 1;

    nodes = 0;
    stopSearch = false;
    startTime = performance.now();
    const baseTime = 3500;
    timeLimit = baseTime;

    let bestMove = legalMoves[0];
    let bestScore = 0;
    const rootMoveScores = new Map();

    // Iterative Deepening + Aspiration Windows + Shannon Entropy Adaptive Time
    for (let depth = 1; depth <= 14; depth++) {
      let delta = 35;
      let alpha = depth >= 4 ? bestScore - delta : -32000;
      let beta = depth >= 4 ? bestScore + delta : 32000;

      while (true) {
        let localBest = bestMove;
        let localScore = -32000;
        const undo = {};
        const scoredList = [];

        legalMoves.sort((a, b) => {
          if (a === bestMove) return -1;
          if (b === bestMove) return 1;
          return (rootMoveScores.get(b) || -99999) - (rootMoveScores.get(a) || -99999);
        });

        let a = alpha;
        for (let i = 0; i < legalMoves.length; i++) {
          const m = legalMoves[i];
          C.makeMove(state, m, undo);
          let s;
          if (i === 0) {
            s = -search(state, depth - 1, -beta, -a, 1, true, m);
          } else {
            s = -search(state, depth - 1, -a - 1, -a, 1, true, m);
            if (s > a && s < beta && !stopSearch) {
              s = -search(state, depth - 1, -beta, -a, 1, true, m);
            }
          }
          C.unmakeMove(state, m, undo);

          if (stopSearch) break;
          scoredList.push({ m, s });
          rootMoveScores.set(m, s);

          if (s > localScore) {
            localScore = s;
            localBest = m;
            if (s > a) a = s;
            if (a >= beta) break;
          }
        }

        if (stopSearch) break;

        if (localScore <= alpha) {
          delta = delta + (delta >> 1) + 20;
          alpha = Math.max(-32000, localScore - delta);
          continue;
        }
        if (localScore >= beta) {
          delta = delta + (delta >> 1) + 20;
          beta = Math.min(32000, localScore + delta);
          continue;
        }

        bestMove = localBest;
        bestScore = localScore;

        // Boltzmann-Gibbs & Shannon Entropy Time Allocation
        if (scoredList.length > 1 && depth >= 4) {
          const T = 65;
          let maxS = -99999;
          for (const item of scoredList) if (item.s > maxS) maxS = item.s;
          let Z = 0;
          const weights = scoredList.map(item => {
            const w = Math.exp(Math.max(-30, (item.s - maxS) / T));
            Z += w;
            return w;
          });
          let H = 0;
          for (const w of weights) {
            const p = w / Z;
            if (p > 1e-9) H -= p * Math.log(p);
          }
          const normH = Math.min(1.0, H / Math.log(scoredList.length));
          timeLimit = Math.min(5200, baseTime * (1 + 0.45 * normH));
        }

        break;
      }

      if (stopSearch || Math.abs(bestScore) > 28000) break;
      if (performance.now() - startTime > timeLimit * 0.62) break;
    }

    return bestMove;
  }

  self.onmessage = function (e) {
    const { state, uciHistory, historyHashes, reqId } = e.data;
    state.board = new Int8Array(state.board);
    const move = findBestMove(state, uciHistory, historyHashes);
    self.postMessage({ move, reqId });
  };
}

/* ============================================================================
   3. PROCEDURAL WEB AUDIO ENGINE
   ============================================================================ */
class SoundFX {
  constructor() { this.ctx = null; }
  init() {
    if (!this.ctx) {
      const AC = window.AudioContext || window.webkitAudioContext;
      if (AC) this.ctx = new AC();
    }
    if (this.ctx && this.ctx.state === 'suspended') this.ctx.resume();
  }
  play(type) {
    this.init();
    if (!this.ctx) return;
    const t = this.ctx.currentTime;
    const osc = this.ctx.createOscillator();
    const gain = this.ctx.createGain();
    osc.connect(gain);
    gain.connect(this.ctx.destination);

    if (type === 'move') {
      osc.type = 'triangle';
      osc.frequency.setValueAtTime(190, t);
      osc.frequency.exponentialRampToValueAtTime(65, t + 0.08);
      gain.gain.setValueAtTime(0.26, t);
      gain.gain.exponentialRampToValueAtTime(0.001, t + 0.09);
      osc.start(t); osc.stop(t + 0.09);
    } else if (type === 'capture') {
      osc.type = 'sawtooth';
      osc.frequency.setValueAtTime(145, t);
      osc.frequency.exponentialRampToValueAtTime(42, t + 0.14);
      gain.gain.setValueAtTime(0.30, t);
      gain.gain.exponentialRampToValueAtTime(0.001, t + 0.15);
      osc.start(t); osc.stop(t + 0.15);
    } else if (type === 'check') {
      osc.type = 'sine';
      osc.frequency.setValueAtTime(520, t);
      osc.frequency.setValueAtTime(680, t + 0.08);
      gain.gain.setValueAtTime(0.22, t);
      gain.gain.exponentialRampToValueAtTime(0.001, t + 0.28);
      osc.start(t); osc.stop(t + 0.28);
    } else if (type === 'gameover') {
      osc.type = 'triangle';
      osc.frequency.setValueAtTime(440, t);
      osc.frequency.setValueAtTime(330, t + 0.15);
      osc.frequency.setValueAtTime(220, t + 0.3);
      gain.gain.setValueAtTime(0.25, t);
      gain.gain.exponentialRampToValueAtTime(0.001, t + 0.55);
      osc.start(t); osc.stop(t + 0.55);
    }
  }
}

/* ============================================================================
   4. 3D BOARD, STAUNTON PIECES, PHYSICS KINEMATICS & CONTROLLER
   ============================================================================ */
(function initApp() {
  const C = createChessCore();
  const sfx = new SoundFX();

  const workerBlob = new Blob(
    [createChessCore.toString() + '\n(' + chessWorkerMain.toString() + ')();'],
    { type: 'application/javascript' }
  );
  const aiWorker = new Worker(URL.createObjectURL(workerBlob));

  // --- Game State ---
  let state = C.createInitialState();
  let gameMode = 'ai'; // 'ai' (Computer) | 'pvp' (Local Player)
  const humanSide = 1; // Player plays White vs Computer
  let aiThinking = false;
  let aiRequestId = 0;
  let gameOver = false;
  let selectedSq = -1;
  let legalMovesCache = C.generateLegalMoves(state);
  let lastMove = null;
  let pendingPromo = null;
  let uciHistory = [];
  let hashHistory = [state.hHi * 4294967296 + state.hLo];

  // --- Three.js Scene ---
  const container = document.getElementById('canvas-container');
  const scene = new THREE.Scene();
  scene.fog = new THREE.FogExp2(0x0b0e14, 0.02);

  const camera = new THREE.PerspectiveCamera(42, container.clientWidth / container.clientHeight, 0.1, 100);
  camera.position.set(0, 9.2, 9.5);

  const renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true });
  renderer.setSize(container.clientWidth, container.clientHeight);
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  renderer.shadowMap.enabled = true;
  renderer.shadowMap.type = THREE.PCFSoftShadowMap;
  renderer.toneMapping = THREE.ACESFilmicToneMapping;
  renderer.toneMappingExposure = 1.08;
  container.appendChild(renderer.domElement);

  const controls = new THREE.OrbitControls(camera, renderer.domElement);
  controls.enableDamping = true;
  controls.dampingFactor = 0.07;
  controls.maxPolarAngle = Math.PI / 2.08;
  controls.minDistance = 5.5;
  controls.maxDistance = 20;
  controls.target.set(0, 0.2, 0);

  // Studio Lighting (balanced so board tiles have crisp contrast without glare)
  scene.add(new THREE.AmbientLight(0xdce6f7, 0.6));

  const keyLight = new THREE.DirectionalLight(0xfff5e4, 1.15);
  keyLight.position.set(7, 15, 9);
  keyLight.castShadow = true;
  keyLight.shadow.mapSize.set(2048, 2048);
  keyLight.shadow.camera.near = 2;
  keyLight.shadow.camera.far = 32;
  const d = 6.5;
  keyLight.shadow.camera.left = -d;
  keyLight.shadow.camera.right = d;
  keyLight.shadow.camera.top = d;
  keyLight.shadow.camera.bottom = -d;
  keyLight.shadow.bias = -0.0005;
  scene.add(keyLight);

  const rimLight = new THREE.DirectionalLight(0x7aa2f7, 0.45);
  rimLight.position.set(-8, 8, -9);
  scene.add(rimLight);

  // --- Procedural Wood Grain Materials ---
  function makeWoodTexture(baseHex, grainHex) {
    const cv = document.createElement('canvas');
    cv.width = 256; cv.height = 256;
    const ctx = cv.getContext('2d');
    ctx.fillStyle = baseHex;
    ctx.fillRect(0, 0, 256, 256);
    ctx.strokeStyle = grainHex;
    ctx.globalAlpha = 0.22;
    for (let i = 0; i < 65; i++) {
      ctx.beginPath();
      const y = Math.random() * 256;
      ctx.lineWidth = 1 + Math.random() * 2.4;
      ctx.moveTo(0, y);
      ctx.bezierCurveTo(85, y + (Math.random() - 0.5) * 14, 170, y + (Math.random() - 0.5) * 14, 256, y);
      ctx.stroke();
    }
    const tex = new THREE.CanvasTexture(cv);
    tex.wrapS = tex.wrapT = THREE.RepeatWrapping;
    return tex;
  }

  const lightWoodMat = new THREE.MeshStandardMaterial({
    map: makeWoodTexture('#ebd8b7', '#c5a474'),
    roughness: 0.55,
    metalness: 0.04
  });
  const darkWoodMat = new THREE.MeshStandardMaterial({
    map: makeWoodTexture('#5c3a24', '#331c0e'),
    roughness: 0.58,
    metalness: 0.05
  });
  const frameMat = new THREE.MeshStandardMaterial({
    map: makeWoodTexture('#24150e', '#0d0704'),
    roughness: 0.42,
    metalness: 0.14
  });
  const goldTrimMat = new THREE.MeshStandardMaterial({
    color: 0xd4af37,
    roughness: 0.3,
    metalness: 0.85
  });

  // --- Build 3D Chessboard (Fixed Y-layering so all 64 tiles show cleanly) ---
  const boardGroup = new THREE.Group();
  scene.add(boardGroup);

  // Outer Wooden Frame: top face at y = -0.02
  const frameMesh = new THREE.Mesh(new THREE.BoxGeometry(9.2, 0.40, 9.2), frameMat);
  frameMesh.position.y = -0.22;
  frameMesh.receiveShadow = true;
  boardGroup.add(frameMesh);

  // Gold Inlay Trim: top face at y = -0.01 (strictly below the 64 squares at y = 0.00)
  const trimMesh = new THREE.Mesh(new THREE.BoxGeometry(8.18, 0.40, 8.18), goldTrimMat);
  trimMesh.position.y = -0.21;
  trimMesh.receiveShadow = true;
  boardGroup.add(trimMesh);

  // Pedestal Base
  const tableMesh = new THREE.Mesh(
    new THREE.CircleGeometry(18, 64),
    new THREE.MeshStandardMaterial({ color: 0x0d1119, roughness: 0.78, metalness: 0.18 })
  );
  tableMesh.rotation.x = -Math.PI / 2;
  tableMesh.position.y = -0.43;
  tableMesh.receiveShadow = true;
  scene.add(tableMesh);

  function sqToWorld(sq) {
    const r = sq >> 3, c = sq & 7;
    return new THREE.Vector3(c - 3.5, 0, r - 3.5);
  }

  // 64 Individual Checkered Squares: top face at y = 0.00 with crisp 0.01 seam
  const squareMeshes = [];
  const sqGeo = new THREE.BoxGeometry(0.99, 0.10, 0.99);
  for (let sq = 0; sq < 64; sq++) {
    const r = sq >> 3, c = sq & 7;
    const isLight = ((r + c) & 1) === 0;
    const mesh = new THREE.Mesh(sqGeo, isLight ? lightWoodMat : darkWoodMat);
    mesh.position.set(c - 3.5, -0.05, r - 3.5);
    mesh.receiveShadow = true;
    mesh.userData = { type: 'square', sq };
    boardGroup.add(mesh);
    squareMeshes[sq] = mesh;
  }

  // Board Coordinates (a-h, 1-8) sitting flush on the outer wood frame (y = -0.016)
  function addCoordLabel(text, x, z) {
    const cv = document.createElement('canvas');
    cv.width = 64; cv.height = 64;
    const ctx = cv.getContext('2d');
    ctx.fillStyle = '#d4af37';
    ctx.font = 'bold 34px sans-serif';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText(text, 32, 34);
    const mat = new THREE.MeshBasicMaterial({ map: new THREE.CanvasTexture(cv), transparent: true });
    const plane = new THREE.Mesh(new THREE.PlaneGeometry(0.42, 0.42), mat);
    plane.rotation.x = -Math.PI / 2;
    plane.position.set(x, -0.016, z);
    boardGroup.add(plane);
  }
  for (let i = 0; i < 8; i++) {
    addCoordLabel('abcdefgh'[i], i - 3.5, 4.35);
    addCoordLabel('abcdefgh'[i], i - 3.5, -4.35);
    addCoordLabel(String(8 - i), -4.35, i - 3.5);
    addCoordLabel(String(8 - i), 4.35, i - 3.5);
  }

  // Highlights Layer
  const highlightGroup = new THREE.Group();
  scene.add(highlightGroup);

  function createRing(innerR, outerR, colorHex, opacity = 0.88) {
    const mesh = new THREE.Mesh(
      new THREE.RingGeometry(innerR, outerR, 32),
      new THREE.MeshBasicMaterial({ color: colorHex, transparent: true, opacity, side: THREE.DoubleSide })
    );
    mesh.rotation.x = -Math.PI / 2;
    mesh.position.y = 0.014;
    return mesh;
  }

  function createTileOverlay(colorHex, opacity = 0.36) {
    const mesh = new THREE.Mesh(
      new THREE.PlaneGeometry(0.97, 0.97),
      new THREE.MeshBasicMaterial({ color: colorHex, transparent: true, opacity })
    );
    mesh.rotation.x = -Math.PI / 2;
    mesh.position.y = 0.008;
    return mesh;
  }

  // --- Sculpted 3D Staunton Pieces ---
  const whitePieceMat = new THREE.MeshStandardMaterial({ color: 0xf4eee0, roughness: 0.25, metalness: 0.06 });
  const blackPieceMat = new THREE.MeshStandardMaterial({ color: 0x1b1f29, roughness: 0.24, metalness: 0.32 });

  function latheProfile(pts) {
    return new THREE.LatheGeometry(pts.map(([x, y]) => new THREE.Vector2(x, y)), 28);
  }

  function buildPieceMesh(pieceCode) {
    const isWhite = pieceCode > 0;
    const type = Math.abs(pieceCode);
    const mat = isWhite ? whitePieceMat : blackPieceMat;
    const g = new THREE.Group();

    const addPart = (geo, m = mat, y = 0) => {
      const mesh = new THREE.Mesh(geo, m);
      mesh.position.y = y;
      mesh.castShadow = true;
      mesh.receiveShadow = true;
      g.add(mesh);
      return mesh;
    };

    addPart(new THREE.TorusGeometry(0.31, 0.018, 10, 28), goldTrimMat, 0.09).rotation.x = Math.PI / 2;

    if (type === C.WP) {
      addPart(latheProfile([[0,0],[0.32,0],[0.32,0.08],[0.24,0.16],[0.15,0.45],[0.19,0.52],[0.11,0.58],[0,0.58]]));
      addPart(new THREE.SphereGeometry(0.16, 20, 20), mat, 0.72);
    } else if (type === C.WR) {
      addPart(latheProfile([[0,0],[0.35,0],[0.35,0.09],[0.27,0.18],[0.20,0.68],[0.26,0.78],[0.26,0.92],[0,0.92]]));
      for (let i = 0; i < 6; i++) {
        const ang = (i / 6) * Math.PI * 2;
        const merlon = addPart(new THREE.BoxGeometry(0.11, 0.14, 0.09), mat, 0.99);
        merlon.position.x = Math.cos(ang) * 0.20;
        merlon.position.z = Math.sin(ang) * 0.20;
        merlon.rotation.y = -ang;
      }
    } else if (type === C.WN) {
      addPart(latheProfile([[0,0],[0.35,0],[0.35,0.09],[0.26,0.20],[0.20,0.34],[0,0.34]]));
      const shape = new THREE.Shape();
      shape.moveTo(-0.16, 0.28);
      shape.quadraticCurveTo(-0.22, 0.65, -0.05, 0.96);
      shape.lineTo(0.06, 1.08);
      shape.lineTo(0.10, 0.94);
      shape.quadraticCurveTo(0.27, 0.85, 0.25, 0.66);
      shape.lineTo(0.14, 0.62);
      shape.quadraticCurveTo(0.10, 0.48, 0.18, 0.28);
      shape.closePath();
      const ext = new THREE.ExtrudeGeometry(shape, { depth: 0.20, bevelEnabled: true, bevelThickness: 0.035, bevelSize: 0.03, bevelSegments: 4 });
      ext.center();
      const head = addPart(ext, mat, 0.68);
      head.rotation.y = isWhite ? Math.PI / 2 : -Math.PI / 2;
    } else if (type === C.WB) {
      addPart(latheProfile([[0,0],[0.35,0],[0.35,0.09],[0.26,0.18],[0.16,0.68],[0.21,0.75],[0.14,0.82],[0.20,0.96],[0.12,1.12],[0,1.16]]));
      addPart(new THREE.SphereGeometry(0.06, 16, 16), goldTrimMat, 1.21);
      addPart(new THREE.TorusGeometry(0.16, 0.018, 8, 24), goldTrimMat, 0.74).rotation.x = Math.PI / 2;
    } else if (type === C.WQ) {
      addPart(latheProfile([[0,0],[0.37,0],[0.37,0.10],[0.28,0.20],[0.17,0.82],[0.24,0.92],[0.16,1.02],[0.24,1.20],[0,1.18]]));
      for (let i = 0; i < 8; i++) {
        const ang = (i / 8) * Math.PI * 2;
        const pearl = addPart(new THREE.SphereGeometry(0.04, 12, 12), goldTrimMat, 1.25);
        pearl.position.x = Math.cos(ang) * 0.20;
        pearl.position.z = Math.sin(ang) * 0.20;
      }
      addPart(new THREE.SphereGeometry(0.085, 18, 18), goldTrimMat, 1.32);
    } else if (type === C.WK) {
      addPart(latheProfile([[0,0],[0.39,0],[0.39,0.10],[0.30,0.22],[0.18,0.92],[0.26,1.04],[0.18,1.14],[0.24,1.32],[0,1.34]]));
      addPart(new THREE.BoxGeometry(0.07, 0.28, 0.07), goldTrimMat, 1.48);
      addPart(new THREE.BoxGeometry(0.22, 0.065, 0.07), goldTrimMat, 1.52);
    }

    g.userData = { type: 'piece', pieceCode };
    return g;
  }

  // --- Physics Kinematics & Camera Spring ---
  const pieceMeshes = new Array(64).fill(null);
  const activeKinematics = [];
  const flyingCaptures = [];
  const GRAVITY = 18.0;

  const camSpring = {
    active: false,
    pos: new THREE.Vector3(),
    vel: new THREE.Vector3(),
    targetPos: new THREE.Vector3(),
    stiffness: 38.0
  };

  function animateCameraTo(x, y, z) {
    camSpring.pos.copy(camera.position);
    camSpring.vel.set(0, 0, 0);
    camSpring.targetPos.set(x, y, z);
    camSpring.active = true;
  }

  function rebuildBoardMeshes() {
    for (let sq = 0; sq < 64; sq++) {
      if (pieceMeshes[sq]) {
        scene.remove(pieceMeshes[sq]);
        pieceMeshes[sq] = null;
      }
      const p = state.board[sq];
      if (p !== 0) {
        const mesh = buildPieceMesh(p);
        mesh.position.copy(sqToWorld(sq));
        mesh.userData.sq = sq;
        scene.add(mesh);
        pieceMeshes[sq] = mesh;
      }
    }
    activeKinematics.length = 0;
  }

  function launchCapturedPiece(mesh, impactDir) {
    const dir = impactDir.clone().normalize();
    flyingCaptures.push({
      mesh,
      vel: new THREE.Vector3(
        dir.x * (3.2 + Math.random() * 1.4) + (Math.random() - 0.5) * 1.5,
        4.6 + Math.random() * 1.5,
        dir.z * (3.2 + Math.random() * 1.4) + (Math.random() - 0.5) * 1.5
      ),
      omega: new THREE.Vector3(
        (Math.random() - 0.5) * 12,
        (Math.random() - 0.5) * 8,
        (Math.random() - 0.5) * 12
      ),
      life: 0
    });
  }

  function animateMove3D(move, movedPiece, capturedSq) {
    const from = move & 63;
    const to = (move >> 6) & 63;
    const promo = (move >> 12) & 7;
    const flags = (move >> 15) & 7;

    const movingMesh = pieceMeshes[from];
    const startPos = sqToWorld(from);
    const endPos = sqToWorld(to);
    const impactDir = endPos.clone().sub(startPos);

    if (capturedSq !== -1 && pieceMeshes[capturedSq]) {
      launchCapturedPiece(pieceMeshes[capturedSq], impactDir);
      pieceMeshes[capturedSq] = null;
    }

    pieceMeshes[from] = null;

    let finalMesh = movingMesh;
    if (promo) {
      if (movingMesh) scene.remove(movingMesh);
      finalMesh = buildPieceMesh((movedPiece > 0 ? 1 : -1) * promo);
      finalMesh.position.copy(startPos);
      scene.add(finalMesh);
    }

    if (finalMesh) {
      finalMesh.userData.sq = to;
      pieceMeshes[to] = finalMesh;
      const isKnight = Math.abs(movedPiece) === C.WN;
      const hMax = isKnight ? 1.55 : 0.25;
      const v0y = Math.sqrt(2 * GRAVITY * hMax);
      const duration = isKnight ? (2 * v0y) / GRAVITY : 0.30;

      activeKinematics.push({
        mesh: finalMesh,
        start: startPos,
        end: endPos,
        isParabolic: isKnight,
        v0y,
        t: 0,
        duration,
        settling: false,
        springY: 0,
        springVy: -2.2
      });
    }

    if (flags & C.FLAG_CASTLE) {
      let rFrom = 0, rTo = 0;
      if (to === 62) { rFrom = 63; rTo = 61; }
      else if (to === 58) { rFrom = 56; rTo = 59; }
      else if (to === 6) { rFrom = 7; rTo = 5; }
      else if (to === 2) { rFrom = 0; rTo = 3; }
      const rMesh = pieceMeshes[rFrom];
      if (rMesh) {
        pieceMeshes[rFrom] = null;
        pieceMeshes[rTo] = rMesh;
        rMesh.userData.sq = rTo;
        activeKinematics.push({
          mesh: rMesh,
          start: sqToWorld(rFrom),
          end: sqToWorld(rTo),
          isParabolic: false,
          v0y: 0,
          t: 0,
          duration: 0.32,
          settling: false,
          springY: 0,
          springVy: -1.2
        });
      }
    }
  }

  function renderHighlights() {
    while (highlightGroup.children.length) highlightGroup.remove(highlightGroup.children[0]);

    if (lastMove !== null) {
      const f = lastMove & 63, t = (lastMove >> 6) & 63;
      const o1 = createTileOverlay(0xd4af37, 0.35);
      o1.position.copy(sqToWorld(f)).setY(0.008);
      const o2 = createTileOverlay(0xd4af37, 0.45);
      o2.position.copy(sqToWorld(t)).setY(0.008);
      highlightGroup.add(o1, o2);
    }

    if (C.inCheck(state, state.turn)) {
      const kSq = state.turn === 1 ? state.wKing : state.bKing;
      const chk = createTileOverlay(0xef4444, 0.58);
      chk.position.copy(sqToWorld(kSq)).setY(0.01);
      highlightGroup.add(chk);
    }

    if (selectedSq !== -1) {
      const sel = createTileOverlay(0x38bdf8, 0.48);
      sel.position.copy(sqToWorld(selectedSq)).setY(0.011);
      highlightGroup.add(sel);

      const moves = legalMovesCache.filter(m => (m & 63) === selectedSq);
      const seenTargets = new Set();
      for (const m of moves) {
        const to = (m >> 6) & 63;
        if (seenTargets.has(to)) continue;
        seenTargets.add(to);
        const isCap = ((m >> 15) & C.FLAG_CAPTURE) !== 0;
        const ring = isCap ? createRing(0.32, 0.44, 0xef4444, 0.92) : createRing(0.11, 0.21, 0x10b981, 0.9);
        ring.position.copy(sqToWorld(to)).setY(0.015);
        highlightGroup.add(ring);
      }
    }
  }

  // --- Pointer / Raycasting ---
  const raycaster = new THREE.Raycaster();
  const pointer = new THREE.Vector2();
  let pointerDownPos = { x: 0, y: 0 };

  renderer.domElement.addEventListener('pointerdown', (e) => {
    pointerDownPos = { x: e.clientX, y: e.clientY };
    camSpring.active = false;
  });

  renderer.domElement.addEventListener('pointerup', (e) => {
    const dist = Math.hypot(e.clientX - pointerDownPos.x, e.clientY - pointerDownPos.y);
    if (dist > 6) return;
    if (gameOver || aiThinking || pendingPromo) return;
    if (gameMode === 'ai' && state.turn !== humanSide) return;

    const rect = renderer.domElement.getBoundingClientRect();
    pointer.x = ((e.clientX - rect.left) / rect.width) * 2 - 1;
    pointer.y = -((e.clientY - rect.top) / rect.height) * 2 + 1;
    raycaster.setFromCamera(pointer, camera);

    const pieceObjs = pieceMeshes.filter(Boolean);
    const hits = raycaster.intersectObjects([...pieceObjs, ...squareMeshes], true);
    if (!hits.length) return;

    let obj = hits[0].object;
    while (obj && obj.userData.sq === undefined && obj.parent) obj = obj.parent;
    const sq = obj ? obj.userData.sq : undefined;
    if (sq === undefined) return;

    handleSquareClick(sq);
  });

  function handleSquareClick(sq) {
    const clickedPiece = state.board[sq];

    if (selectedSq !== -1) {
      const matching = legalMovesCache.filter(m => (m & 63) === selectedSq && ((m >> 6) & 63) === sq);
      if (matching.length > 0) {
        if (matching.some(m => ((m >> 12) & 7) !== 0)) {
          pendingPromo = matching;
          document.getElementById('promo-modal').classList.remove('hidden');
          return;
        }
        commitMove(matching[0]);
        return;
      }
    }

    if (clickedPiece !== 0 && (clickedPiece > 0 ? 1 : -1) === state.turn) {
      selectedSq = selectedSq === sq ? -1 : sq;
    } else {
      selectedSq = -1;
    }
    renderHighlights();
  }

  function commitMove(move) {
    const from = move & 63;
    const to = (move >> 6) & 63;
    const flags = (move >> 15) & 7;
    const movedPiece = state.board[from];

    let capturedSq = -1;
    let capPiece = 0;
    if (flags & C.FLAG_EP) {
      capturedSq = state.turn === 1 ? to + 8 : to - 8;
      capPiece = state.board[capturedSq];
    } else if (state.board[to] !== 0) {
      capturedSq = to;
      capPiece = state.board[to];
    }

    const undo = {};
    C.makeMove(state, move, undo);
    animateMove3D(move, movedPiece, capturedSq);

    lastMove = move;
    selectedSq = -1;
    uciHistory.push(C.moveToUci(move));
    hashHistory.push(state.hHi * 4294967296 + state.hLo);
    legalMovesCache = C.generateLegalMoves(state);

    const nowInCheck = C.inCheck(state, state.turn);
    if (nowInCheck) sfx.play('check');
    else if (capPiece !== 0) sfx.play('capture');
    else sfx.play('move');

    renderHighlights();
    updateTurnUI();
    checkGameStatus();

    if (!gameOver) {
      if (gameMode === 'pvp') {
        if (state.turn === 1) animateCameraTo(0, 9.2, 9.5);
        else animateCameraTo(0, 9.2, -9.5);
      } else if (gameMode === 'ai' && state.turn !== humanSide) {
        requestAIMove();
      }
    }
  }

  function checkGameStatus() {
    const curKey = state.hHi * 4294967296 + state.hLo;
    let repCount = 0;
    for (const h of hashHistory) if (h === curKey) repCount++;

    let title = '', sub = '';
    if (legalMovesCache.length === 0) {
      if (C.inCheck(state, state.turn)) {
        title = 'Checkmate';
        sub = (state.turn === 1 ? 'Black' : 'White') + ' wins the match!';
      } else {
        title = 'Stalemate';
        sub = 'Draw — no legal moves remaining.';
      }
    } else if (state.halfmove >= 100) {
      title = 'Draw (50-Move Rule)';
      sub = '50 moves without capture or pawn advance.';
    } else if (repCount >= 3) {
      title = 'Draw (Threefold Repetition)';
      sub = 'Identical position repeated 3 times.';
    } else if (C.isInsufficientMaterial(state)) {
      title = 'Draw (Insufficient Material)';
      sub = 'Neither side can force checkmate.';
    }

    if (title) {
      gameOver = true;
      sfx.play('gameover');
      document.getElementById('gameover-title').textContent = title;
      document.getElementById('gameover-sub').textContent = sub;
      document.getElementById('gameover-modal').classList.remove('hidden');
    }
  }

  function requestAIMove() {
    aiThinking = true;
    const reqId = ++aiRequestId;
    document.getElementById('thinking-pill').classList.remove('hidden');

    aiWorker.postMessage({
      state: C.cloneState(state),
      uciHistory: [...uciHistory],
      historyHashes: [...hashHistory],
      reqId
    });
  }

  aiWorker.onmessage = function (e) {
    const { move, reqId } = e.data;
    if (reqId !== aiRequestId) return; // Ignore stale search if match restarted
    aiThinking = false;
    document.getElementById('thinking-pill').classList.add('hidden');
    if (move && !gameOver && gameMode === 'ai' && state.turn !== humanSide) {
      commitMove(move);
    }
  };

  function updateTurnUI() {
    const dot = document.getElementById('turn-dot');
    const txt = document.getElementById('turn-text');
    dot.className = 'turn-dot ' + (state.turn === 1 ? 'white' : 'black');
    const chkStr = C.inCheck(state, state.turn) ? ' — CHECK!' : '';
    txt.textContent = (state.turn === 1 ? 'White to Move' : 'Black to Move') + chkStr;
  }

  function restartMatch() {
    aiRequestId++;
    aiThinking = false;
    gameOver = false;
    pendingPromo = null;
    selectedSq = -1;
    lastMove = null;
    state = C.createInitialState();
    legalMovesCache = C.generateLegalMoves(state);
    uciHistory = [];
    hashHistory = [state.hHi * 4294967296 + state.hLo];

    document.getElementById('gameover-modal').classList.add('hidden');
    document.getElementById('promo-modal').classList.add('hidden');
    document.getElementById('thinking-pill').classList.add('hidden');

    for (const f of flyingCaptures) scene.remove(f.mesh);
    flyingCaptures.length = 0;

    rebuildBoardMeshes();
    renderHighlights();
    updateTurnUI();
    animateCameraTo(0, 9.2, 9.5);
  }

  // --- Controls ---
  document.querySelectorAll('.ctrl-btn[data-mode]').forEach(btn => {
    btn.addEventListener('click', () => {
      document.querySelectorAll('.ctrl-btn[data-mode]').forEach(b => b.classList.remove('active'));
      btn.classList.add('active');
      gameMode = btn.dataset.mode;
      restartMatch();
    });
  });

  document.getElementById('btn-restart').addEventListener('click', restartMatch);
  document.getElementById('btn-rematch').addEventListener('click', restartMatch);

  document.querySelectorAll('.promo-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      if (!pendingPromo) return;
      const pCode = parseInt(btn.dataset.promo, 10);
      const chosen = pendingPromo.find(m => ((m >> 12) & 7) === pCode) || pendingPromo[0];
      pendingPromo = null;
      document.getElementById('promo-modal').classList.add('hidden');
      commitMove(chosen);
    });
  });

  window.addEventListener('resize', () => {
    camera.aspect = container.clientWidth / container.clientHeight;
    camera.updateProjectionMatrix();
    renderer.setSize(container.clientWidth, container.clientHeight);
  });

  // --- 60 FPS Physics & Render Loop ---
  const clock = new THREE.Clock();

  function animate() {
    requestAnimationFrame(animate);
    const dt = Math.min(0.05, clock.getDelta());

    if (camSpring.active) {
      const k = camSpring.stiffness;
      const c = 2 * Math.sqrt(k);
      const disp = camSpring.pos.clone().sub(camSpring.targetPos);
      const acc = disp.multiplyScalar(-k).add(camSpring.vel.clone().multiplyScalar(-c));
      camSpring.vel.add(acc.multiplyScalar(dt));
      camSpring.pos.add(camSpring.vel.clone().multiplyScalar(dt));
      camera.position.copy(camSpring.pos);
      if (camSpring.pos.distanceTo(camSpring.targetPos) < 0.02 && camSpring.vel.length() < 0.02) {
        camera.position.copy(camSpring.targetPos);
        camSpring.active = false;
      }
    }

    for (let i = activeKinematics.length - 1; i >= 0; i--) {
      const k = activeKinematics[i];
      if (!k.settling) {
        k.t += dt;
        const u = Math.min(1, k.t / k.duration);
        const s = u * u * (3 - 2 * u);
        k.mesh.position.x = k.start.x + (k.end.x - k.start.x) * s;
        k.mesh.position.z = k.start.z + (k.end.z - k.start.z) * s;

        if (k.isParabolic) {
          const ty = u * k.duration;
          k.mesh.position.y = Math.max(0, k.v0y * ty - 0.5 * GRAVITY * ty * ty);
        } else {
          k.mesh.position.y = Math.sin(u * Math.PI) * 0.14;
        }

        if (u >= 1) {
          k.mesh.position.set(k.end.x, 0, k.end.z);
          k.settling = true;
        }
      } else {
        const stiff = 260;
        const damp = 2 * Math.sqrt(stiff);
        const ay = -stiff * k.springY - damp * k.springVy;
        k.springVy += ay * dt;
        k.springY += k.springVy * dt;
        k.mesh.position.y = Math.max(0, -k.springY * 0.06);
        if (Math.abs(k.springY) < 0.002 && Math.abs(k.springVy) < 0.01) {
          k.mesh.position.y = 0;
          activeKinematics.splice(i, 1);
        }
      }
    }

    if (selectedSq !== -1 && pieceMeshes[selectedSq] && activeKinematics.length === 0) {
      pieceMeshes[selectedSq].position.y = 0.22 + Math.sin(performance.now() * 0.006) * 0.06;
    }

    for (let i = flyingCaptures.length - 1; i >= 0; i--) {
      const f = flyingCaptures[i];
      f.life += dt;
      f.vel.y -= GRAVITY * dt;
      f.mesh.position.addScaledVector(f.vel, dt);
      f.mesh.rotation.x += f.omega.x * dt;
      f.mesh.rotation.y += f.omega.y * dt;
      f.mesh.rotation.z += f.omega.z * dt;

      if (f.mesh.position.y < -0.4 && f.life > 0.4) {
        f.mesh.position.y = -0.4;
        f.vel.y *= -0.35;
        f.vel.x *= 0.72;
        f.vel.z *= 0.72;
        f.omega.multiplyScalar(0.68);
      }
      if (f.life > 1.8) {
        f.mesh.scale.multiplyScalar(0.88);
        if (f.mesh.scale.x < 0.05) {
          scene.remove(f.mesh);
          flyingCaptures.splice(i, 1);
        }
      }
    }

    controls.update();
    renderer.render(scene, camera);
  }

  restartMatch();
  animate();
})();