// ---- lean-js runtime prelude (minimal) ----
function lean_apply(clo, more) {
  if (typeof clo === 'function') return clo(...more);
  const all = clo.args.concat(more);
  return clo.fn(...all);
}

function double(x_1) {
  const x_2 = (x_1 + x_1);
  return x_2;
}

function mkShifted(x_1) {
  const x_2 = 0;
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

