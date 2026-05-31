// ===================== lean-js runtime prelude =====================
// Representation choices:
//   Nat  -> bigint (>= 0n)        Int   -> bigint
//   Bool -> boolean (scalar)      Char  -> number (code point)
//   String -> JS string (code-point semantics)
//   Array<T> -> T[]               List<T> -> tagged ctor objects {tag, fields}
// Bool is lowered to a scalar (false=0, true=1) matched by the emitted
// `switch`, so decEq/decLt/decLe and other Bool-returning externs return the
// number 0 or 1 (NOT a JS boolean: `switch (true)` would not hit `case 1`).
const L_bool = (b) => (b ? 1 : 0);

// Constructor tag of a value. Nullary ctors of a multi-ctor inductive (e.g.
// List.nil, Bool.false) are lowered to the bare number cidx (like lean_box);
// ctors with fields are objects { tag, fields }. lean_obj_tag handles both.
const lean_tag = (x) => (typeof x === 'number' ? x : x.tag);

// ---- closure application (pap/ap model) ----
function lean_apply(clo, more) {
  if (typeof clo === 'function') return clo(...more);
  const all = clo.args.concat(more);
  return clo.fn(...all);
}

// ---- Nat (bigint, total: /0 and %0 -> 0/lhs; sub is truncated monus) ----
const lean_nat_pow = (a, b) => a ** b;
const lean_nat_pred = (a) => (a > 0n ? a - 1n : 0n);
const lean_nat_gcd = (a, b) => { while (b) { [a, b] = [b, a % b]; } return a; };
const lean_nat_dec_eq = (a, b) => L_bool(a === b);
const lean_nat_dec_lt = (a, b) => L_bool(a < b);
const lean_nat_dec_le = (a, b) => L_bool(a <= b);

// ---- Int (bigint). div/mod = T-rounding; ediv/emod = Euclidean. ----
const lean_int_neg = (a) => -a;
const lean_int_div = (a, b) => (b === 0n ? 0n : a / b);
const lean_int_mod = (a, b) => (b === 0n ? a : a % b);
const lean_int_emod = (a, b) => {
  if (b === 0n) return a;
  const r = a % b;
  return r < 0n ? r + (b < 0n ? -b : b) : r;
};
const lean_int_ediv = (a, b) => {
  if (b === 0n) return 0n;
  const q = a / b, r = a % b;
  return r < 0n ? (b > 0n ? q - 1n : q + 1n) : q;
};
const lean_int_dec_eq = (a, b) => L_bool(a === b);
const lean_int_dec_lt = (a, b) => L_bool(a < b);
const lean_int_dec_le = (a, b) => L_bool(a <= b);

// ---- Char ----
const lean_uint32_of_nat = (n) => Number(n & 0xffffffffn);

// ---- String: UTF-8 / code-point semantics ----
const lean_string_length = (s) => BigInt([...s].length);
const lean_string_append = (a, b) => a + b;
const lean_string_push = (s, c) => s + String.fromCodePoint(c);
const lean_string_dec_eq = (a, b) => L_bool(a === b);
const lean_string_isempty = (s) => L_bool(s.length === 0);
const lean_string_hash = (s) => { let h = 0n; for (const c of s) { h = (h * 31n + BigInt(c.codePointAt(0))) & 0xffffffffffffffffn; } return h; };
// String.data / String.toList -> List Char (code points): tag 0 = nil, tag 1 = cons{head,tail}
const lean_string_data = (s) =>
  [...s].reduceRight((tl, ch) => ({ tag: 1, fields: [ch.codePointAt(0), tl] }), 0);
// String.mk : List Char -> String
const lean_string_mk = (lst) => {
  let out = '';
  let cur = lst;
  while (typeof cur !== 'number' && cur.tag === 1) {
    out += String.fromCodePoint(cur.fields[0]);
    cur = cur.fields[1];
  }
  return out;
};

// ---- Array: JS array. get is bounds-checked w/ default; push mutates. ----
const lean_array_get_size = (a) => BigInt(a.length);
const lean_array_fget = (a, i) => a[Number(i)];
const lean_array_get = (a, i, dflt) => {
  const idx = Number(i); return idx >= 0 && idx < a.length ? a[idx] : dflt;
};
const lean_array_uget = (a, i) => a[Number(i)];
const lean_array_set = (a, i, v) => { a[Number(i)] = v; return a; };
const lean_array_push = (a, v) => { a.push(v); return a; };
const lean_array_pop = (a) => { a.pop(); return a; };
const lean_array_swap = (a, i, j) => {
  const x = Number(i), y = Number(j); [a[x], a[y]] = [a[y], a[x]]; return a;
};

// ================ GENERATED ================

function LeanJs_Demo_double(x_1) {
  const x_2 = (x_1 + x_1);
  return x_2;
}

function LeanJs_Demo_mkShifted(x_1) {
  const x_2 = 1;
  switch (x_2) {
    case 0: {
      const x_3 = x_1.fields[0];
      const x_4 = x_1.fields[1];
      const x_5 = 1n;
      const x_6 = (x_3 + x_5);
      const x_7 = (x_4 + x_3);
      x_1.fields[1] = x_7;
      x_1.fields[0] = x_6;
      return x_1;
    }
    case 1: {
      const x_8 = x_1.fields[0];
      const x_9 = x_1.fields[1];
      const x_10 = 1n;
      const x_11 = (x_8 + x_10);
      const x_12 = (x_9 + x_8);
      const x_13 = { tag: 0, fields: [x_11, x_12] };
      return x_13;
    }
    default: { throw new Error("no matching case"); }
  }
}

function LeanJs_Demo_sumTo_go(x_1, x_2) {
  while (true) {
    const x_3 = 0n;
    const x_4 = lean_nat_dec_eq(x_1, x_3);
    switch (x_4) {
      case 1: {
        return x_2;
      }
      case 0: {
        const x_5 = 1n;
        const x_6 = (x_1 > x_5 ? x_1 - x_5 : 0n);
        const x_7 = (x_6 + x_5);
        const x_8 = (x_2 + x_7);
        const __t_1 = x_6;
        const __t_2 = x_8;
        x_1 = __t_1;
        x_2 = __t_2;
        continue;
      }
      default: { throw new Error("no matching case"); }
    }
  }
}

function LeanJs_Demo_sumTo(x_1) {
  const x_2 = 0n;
  const x_3 = LeanJs_Demo_sumTo_go(x_1, x_2);
  return x_3;
}

// extern Nat_sub -> runtime prelude

// extern Nat_mul -> runtime prelude

function LeanJs_Demo_fact(x_1) {
  const x_2 = 0n;
  const x_3 = lean_nat_dec_eq(x_1, x_2);
  switch (x_3) {
    case 1: {
      const x_4 = 1n;
      return x_4;
    }
    case 0: {
      const x_5 = 1n;
      const x_6 = (x_1 > x_5 ? x_1 - x_5 : 0n);
      const x_7 = (x_6 + x_5);
      const x_8 = LeanJs_Demo_fact(x_6);
      const x_9 = (x_7 * x_8);
      return x_9;
    }
    default: { throw new Error("no matching case"); }
  }
}

// extern Nat_add -> runtime prelude

function LeanTodo_TodoList_add(x_1, x_2) {
  const x_3 = 1;
  switch (x_3) {
    case 0: {
      const x_4 = x_1.fields[0];
      const x_5 = x_1.fields[1];
      const x_6 = 0;
      const x_7 = { tag: 0, fields: [x_5, x_2] };
      x_7.fields[2] = x_6;
      const x_8 = { tag: 1, fields: [x_7, x_4] };
      const x_9 = 1n;
      const x_10 = (x_5 + x_9);
      x_1.fields[1] = x_10;
      x_1.fields[0] = x_8;
      return x_1;
    }
    case 1: {
      const x_11 = x_1.fields[0];
      const x_12 = x_1.fields[1];
      const x_13 = 0;
      const x_14 = { tag: 0, fields: [x_12, x_2] };
      x_14.fields[2] = x_13;
      const x_15 = { tag: 1, fields: [x_14, x_11] };
      const x_16 = 1n;
      const x_17 = (x_12 + x_16);
      const x_18 = { tag: 0, fields: [x_15, x_17] };
      return x_18;
    }
    default: { throw new Error("no matching case"); }
  }
}

function List_mapTR_loop__at__LeanTodo_TodoList_toggle_spec_0(x_1, x_2, x_3) {
  while (true) {
    switch (lean_tag(x_2)) {
      case 0: {
        const x_4 = List_reverse__redArg(x_3);
        return x_4;
      }
      case 1: {
        const x_5 = x_2.fields[0];
        const x_6 = x_2.fields[1];
        const x_7 = null;
        const x_12 = x_5.fields[0];
        const x_13 = x_5.fields[1];
        const x_14 = x_5.fields[2];
        const x_15 = lean_nat_dec_eq(x_12, x_1);
        switch (x_15) {
          case 0: {
            const x_8 = x_5;
            const x_9 = { tag: 1, fields: [x_8, x_3] };
            const __t_1 = x_1;
            const __t_2 = x_6;
            const __t_3 = x_9;
            x_1 = __t_1;
            x_2 = __t_2;
            x_3 = __t_3;
            continue;
          }
          case 1: {
            const x_16 = 1;
            switch (x_16) {
              case 0: {
                const x_17 = x_5.fields[1];
                const x_18 = x_5.fields[0];
                switch (x_14) {
                  case 0: {
                    x_5.fields[2] = x_15;
                    const x_8 = x_5;
                    const x_9 = { tag: 1, fields: [x_8, x_3] };
                    const __t_1 = x_1;
                    const __t_2 = x_6;
                    const __t_3 = x_9;
                    x_1 = __t_1;
                    x_2 = __t_2;
                    x_3 = __t_3;
                    continue;
                  }
                  case 1: {
                    const x_19 = 0;
                    x_5.fields[2] = x_19;
                    const x_8 = x_5;
                    const x_9 = { tag: 1, fields: [x_8, x_3] };
                    const __t_1 = x_1;
                    const __t_2 = x_6;
                    const __t_3 = x_9;
                    x_1 = __t_1;
                    x_2 = __t_2;
                    x_3 = __t_3;
                    continue;
                  }
                  default: { throw new Error("no matching case"); }
                }
              }
              case 1: {
                switch (x_14) {
                  case 0: {
                    const x_20 = { tag: 0, fields: [x_12, x_13] };
                    x_20.fields[2] = x_15;
                    const x_8 = x_20;
                    const x_9 = { tag: 1, fields: [x_8, x_3] };
                    const __t_1 = x_1;
                    const __t_2 = x_6;
                    const __t_3 = x_9;
                    x_1 = __t_1;
                    x_2 = __t_2;
                    x_3 = __t_3;
                    continue;
                  }
                  case 1: {
                    const x_21 = 0;
                    const x_22 = { tag: 0, fields: [x_12, x_13] };
                    x_22.fields[2] = x_21;
                    const x_8 = x_22;
                    const x_9 = { tag: 1, fields: [x_8, x_3] };
                    const __t_1 = x_1;
                    const __t_2 = x_6;
                    const __t_3 = x_9;
                    x_1 = __t_1;
                    x_2 = __t_2;
                    x_3 = __t_3;
                    continue;
                  }
                  default: { throw new Error("no matching case"); }
                }
              }
              default: { throw new Error("no matching case"); }
            }
          }
          default: { throw new Error("no matching case"); }
        }
      }
      default: { throw new Error("no matching case"); }
    }
  }
}

function LeanTodo_TodoList_toggle(x_1, x_2) {
  const x_3 = 1;
  switch (x_3) {
    case 0: {
      const x_4 = x_1.fields[0];
      const x_5 = 0;
      const x_6 = List_mapTR_loop__at__LeanTodo_TodoList_toggle_spec_0(x_2, x_4, x_5);
      x_1.fields[0] = x_6;
      return x_1;
    }
    case 1: {
      const x_7 = x_1.fields[0];
      const x_8 = x_1.fields[1];
      const x_9 = 0;
      const x_10 = List_mapTR_loop__at__LeanTodo_TodoList_toggle_spec_0(x_2, x_7, x_9);
      const x_11 = { tag: 0, fields: [x_10, x_8] };
      return x_11;
    }
    default: { throw new Error("no matching case"); }
  }
}

function List_reverseAux__redArg(x_1, x_2) {
  while (true) {
    switch (lean_tag(x_1)) {
      case 0: {
        return x_2;
      }
      case 1: {
        const x_3 = 1;
        switch (x_3) {
          case 0: {
            const x_4 = x_1.fields[1];
            x_1.fields[1] = x_2;
            const __t_1 = x_4;
            const __t_2 = x_1;
            x_1 = __t_1;
            x_2 = __t_2;
            continue;
          }
          case 1: {
            const x_6 = x_1.fields[0];
            const x_7 = x_1.fields[1];
            const x_8 = { tag: 1, fields: [x_6, x_2] };
            const __t_1 = x_7;
            const __t_2 = x_8;
            x_1 = __t_1;
            x_2 = __t_2;
            continue;
          }
          default: { throw new Error("no matching case"); }
        }
      }
      default: { throw new Error("no matching case"); }
    }
  }
}

function List_reverse__redArg(x_1) {
  const x_2 = 0;
  const x_3 = List_reverseAux__redArg(x_1, x_2);
  return x_3;
}

// extern Nat_decEq -> runtime prelude

function List_filterTR_loop__at__LeanTodo_TodoList_remove_spec_0(x_1, x_2, x_3) {
  while (true) {
    switch (lean_tag(x_2)) {
      case 0: {
        const x_4 = List_reverse__redArg(x_3);
        return x_4;
      }
      case 1: {
        const x_5 = 1;
        switch (x_5) {
          case 0: {
            const x_6 = x_2.fields[0];
            const x_7 = x_2.fields[1];
            const x_8 = x_6.fields[0];
            const x_9 = lean_nat_dec_eq(x_8, x_1);
            switch (x_9) {
              case 0: {
                x_2.fields[1] = x_3;
                const __t_1 = x_1;
                const __t_2 = x_7;
                const __t_3 = x_2;
                x_1 = __t_1;
                x_2 = __t_2;
                x_3 = __t_3;
                continue;
              }
              case 1: {
                const __t_1 = x_1;
                const __t_2 = x_7;
                const __t_3 = x_3;
                x_1 = __t_1;
                x_2 = __t_2;
                x_3 = __t_3;
                continue;
              }
              default: { throw new Error("no matching case"); }
            }
          }
          case 1: {
            const x_12 = x_2.fields[0];
            const x_13 = x_2.fields[1];
            const x_14 = x_12.fields[0];
            const x_15 = lean_nat_dec_eq(x_14, x_1);
            switch (x_15) {
              case 0: {
                const x_16 = { tag: 1, fields: [x_12, x_3] };
                const __t_1 = x_1;
                const __t_2 = x_13;
                const __t_3 = x_16;
                x_1 = __t_1;
                x_2 = __t_2;
                x_3 = __t_3;
                continue;
              }
              case 1: {
                const __t_1 = x_1;
                const __t_2 = x_13;
                const __t_3 = x_3;
                x_1 = __t_1;
                x_2 = __t_2;
                x_3 = __t_3;
                continue;
              }
              default: { throw new Error("no matching case"); }
            }
          }
          default: { throw new Error("no matching case"); }
        }
      }
      default: { throw new Error("no matching case"); }
    }
  }
}

function LeanTodo_TodoList_remove(x_1, x_2) {
  const x_3 = 1;
  switch (x_3) {
    case 0: {
      const x_4 = x_1.fields[0];
      const x_5 = 0;
      const x_6 = List_filterTR_loop__at__LeanTodo_TodoList_remove_spec_0(x_2, x_4, x_5);
      x_1.fields[0] = x_6;
      return x_1;
    }
    case 1: {
      const x_7 = x_1.fields[0];
      const x_8 = x_1.fields[1];
      const x_9 = 0;
      const x_10 = List_filterTR_loop__at__LeanTodo_TodoList_remove_spec_0(x_2, x_7, x_9);
      const x_11 = { tag: 0, fields: [x_10, x_8] };
      return x_11;
    }
    default: { throw new Error("no matching case"); }
  }
}

function LeanTodo_TodoList_step(x_1, x_2) {
  switch (lean_tag(x_2)) {
    case 0: {
      const x_3 = x_2.fields[0];
      const x_4 = LeanTodo_TodoList_add(x_1, x_3);
      return x_4;
    }
    case 1: {
      const x_5 = x_2.fields[0];
      const x_6 = LeanTodo_TodoList_toggle(x_1, x_5);
      return x_6;
    }
    case 2: {
      const x_7 = x_2.fields[0];
      const x_8 = LeanTodo_TodoList_remove(x_1, x_7);
      return x_8;
    }
    default: { throw new Error("no matching case"); }
  }
}

