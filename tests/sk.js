const Assert = require("assert");

describe("S and K", async () => {

  it("MIU", async () => {
    // K[x][y] = x
    // S[x][y][z] = x[z][y[z]]

    // i[x] = x[S][K], I = i[i], K = i[i[i[i]]], S = i[i[i[i[i]]]]
    // m[x][y][z] = x[z][y[K[z]]], K = A (A A) (A (A A) A A A A A), A (A (A A (A A (A A))(A (A (A A (A A)))))) A A
    // w[x] = x[K][S][K], K = w[w][w] and S = w[w[w]]
    // v[x] = x[K][S], S = v[v][v] and K = v[v[v][v][v][v]]
    
    const trees = ["F"];

    // ["F"]
    // ["F", ["F"]], F[F]
    // ["F", ["F"], ["F"]], ["F", ["F", ["F"]]], F[F][F] and F[F[F]]
    // ["F", ["F"], ["F"], ["F"]] (F[F][F][F]),  ["F", ["F", ["F"]], ["F"]] (F[F[F][F]]), ["F", ["F"], ["F", ["F"]]] (F[F][F[F]])
    // ["F", ["F"], ["F", ["F"]]] (F[F][F[F]]), ["F", ["F", ["F"], ["F"]]] (F[F[F][F]]), ["F", ["F", ["F", ["F"]]]] (F[F[F[F]]])
    
    
  });
  
  function match(parent, i, combinator) {
    // console.log(combinator.args);
    if ((i + combinator.args) >= parent.length) {
      return false;
    }
    if (parent[i] != combinator.head) {
      return false;
    }
    return true;
  }
    
  function apply(parent, i, combinator) {
    if (!match(parent, i, combinator)) {
      throw new Error(`Can't apply ${combinator.head}`);
    }
    
    parent.splice(i, combinator.args + 1, ...combinator(parent.slice(i, i + combinator.args + 1)));
    return parent;
  }

  function go(combinators, node) {
    for (let i = 0; i < node.length; i++) {
      if (Array.isArray(node[i])) {
        // console.log("hi");
        go(combinators, node[i]);
        continue;
      }
      while (true) {
        let done = true;
        for (let combinator of combinators) {
          if (match(node, i, combinator)) {
            apply(node, i, combinator);
            // yield [node, i, combinator];
            done = false;
            break;
          }
        }
        if (done) {
          break;
        }
      }
    }
    return node;
  }

  it("iota", async () => {
    const s = "S";
    const k = "K";
    const i = "I";
    
    let I = ([i, [...x]]) => [...x, [s], [k]];
    let K = ([k, [...x], [...y]]) => [...x];
    let S = ([s, [...x], [...y], [...z]]) => [...x, [...z], [...y, [...z]]];

    I.head = "I";
    I.args = 1;

    K.head = "K";
    K.args = 2;

    S.head = "S";
    S.args = 3;

    const x = "x";
    
    const id = [i, [i], [x]];

    assertThat(apply(id, 0, I)).equalsTo([i, [s], [k], [x]]);
    assertThat(apply(id, 0, I)).equalsTo([s, [s], [k], [k], [x]]);
    assertThat(apply(id, 0, S)).equalsTo([s, [k], [k, [k]], [x]]);
    assertThat(apply(id, 0, S)).equalsTo([k, [x], [k, [k], [x]]]);
    assertThat(apply(id, 0, K)).equalsTo([x]);

    assertThat(go([I, K, S], [i, [i], [x]])).equalsTo([x]);

    const y = "y";
    const K_ = [i, [i, [i, [i]]], [x], [y]];

    assertThat(apply(K_, 0, I)).equalsTo([i, [i, [i]], [s], [k], [x], [y]]);
    assertThat(apply(K_, 0, I)).equalsTo([i, [i], [s], [k], [s], [k], [x], [y]]);
    assertThat(apply(K_, 0, I)).equalsTo([i, [s], [k], [s], [k], [s], [k], [x], [y]]);
    assertThat(apply(K_, 0, I)).equalsTo([s, [s], [k], [k], [s], [k], [s], [k], [x], [y]]);
    // s, [s], [k], [k]
    assertThat(apply(K_, 0, S)).equalsTo([s, [k], [k, [k]], [s], [k], [s], [k], [x], [y]]);
    // s, [k], [k, [k]], [s]
    assertThat(apply(K_, 0, S)).equalsTo([k, [s], [k, [k], [s]], [k], [s], [k], [x], [y]]);
    assertThat(apply(K_, 0, K)).equalsTo([s, [k], [s], [k], [x], [y]]);
    // s, [k], [s], [k]
    assertThat(apply(K_, 0, S)).equalsTo([k, [k], [s, [k]], [x], [y]]);
    assertThat(apply(K_, 0, K)).equalsTo([k, [x], [y]]);
    assertThat(apply(K_, 0, K)).equalsTo([x]);

    assertThat(go([I, K, S], [i, [i, [i, [i]]], [x], [y]])).equalsTo([x]);

    const z = "z";
    const S_ = [i, [i, [i, [i, [i]]]], [x], [y], [z]];

    assertThat(go([I, K, S], [i, [i, [i, [i, [i]]]], [x], [y], [z]])).equalsTo([x, [z], [y, [z]]]);
  });
  
  it("A", async () => {
    const A = ([a, [...x], [...y], [...z]]) => [...x, [...z], [...y, ["K", [...z]]]];
    A.head = "A";
    A.args = 3;

    let K_ = ([k, [...x], [...y]]) => [...x];
    K_.head = "K";
    K_.args = 2;

    const T = ["A", [1, [5]], [2], [3]];
    T.splice(0, 4, ...A(T.slice(0, 4)));
    assertThat(T)
      .equalsTo([1, [5], [3], [2, ["K", [3]]]]);

    const U = ["K", [1, [5]], [2]];
    U.splice(0, 3, ...K_(U.slice(0, 3)));
    assertThat(U)
      .equalsTo([1, [5]]);

    const a = 'A';
    const k = 'K';

    const x = 'x';
    const y = 'y';

    // K = A (A A) (A (A A) A A A A A)
    const K = [a, [a, [a]], [a, [a, [a]], [a], [a], [a], [a], [a]], [x], [y]];
    
    assertThat(go([K_, A], JSON.parse(JSON.stringify(K)))).equalsTo([x]);
    
    const z = 'z';

    // S = A (A (A A (A A (A A))(A (A (A A (A A)))))) A A
    const S = [a, [a, [a, [a], [a, [a], [a, [a]]], [a, [a, [a, [a], [a, [a]]]]]]], [a], [a], [x], [y], [z]];
    
    assertThat(go([K_, A], S)).equalsTo([x, [z], [y, [z]]]);
  });

  it("W", async () => {
    const k = "K";
    const s = "S";
    const w = "W";
    const x = "x";
    const y = "y";
    const z = "z";
    
    const S = ([s, [...x], [...y], [...z]]) => [...x, [...z], [...y, [...z]]];
    S.head = s;
    S.args = 3;

    const K = ([k, [...x], [...y]]) => [...x];
    K.head = k;
    K.args = 2;

    const W = ([w, [...x]]) => [...x, [k], [s], [k]];
    W.head = w;
    W.args = 1;

    assertThat(go([S, K, W], [w, w, w, x, y])).equalsTo([x]);
    assertThat(go([S, K, W], [w, [w, [w]], x, y, z])).equalsTo([x, [z], [y, [z]]]);
  });
  
  it("V", async () => {
    const k = "K";
    const s = "S";
    const v = "V";
    const x = "x";
    const y = "y";
    const z = "z";
    
    const S = ([s, [...x], [...y], [...z]]) => [...x, [...z], [...y, [...z]]];
    S.head = s;
    S.args = 3;

    const K = ([k, [...x], [...y]]) => [...x];
    K.head = k;
    K.args = 2;

    const V = ([v, [...x]]) => [...x, [k], [s]];
    V.head = v;
    V.args = 1;

    assertThat(go([S, K, V], [v, v, v, x, y, z])).equalsTo([x, [z], [y, [z]]]);
    assertThat(go([S, K, V], [v, [v, [v], [v], [v], [v]], x, y])).equalsTo([x]);
  });
  

  it("S and K", async () => {
    const S = ([s, [...x], [...y], [...z]]) => [...x, [...z], [...y, [...z]]];
    S.head = "S";
    S.args = 3;

    const K = ([k, [...x], [...y]]) => [...x];
    K.head = "K";
    K.args = 2;

    const s = "S";
    const k = "K";
    const x = "x";
    const I = [s, [k], [k], [x]];

    assertThat(go([S, K], I)).equalsTo([x]);
  });
  
  it("S and K", async () => {
    const file = await require("fs/promises").readFile("tests/sk.tt");
    const src = file.toString();
    const {Compiler} = require("./../src/compiler.js");
    const {Verifier} = require("./../src/descent.js");
    const metamath = await new Compiler().compile(src);

    assertThat(new Verifier().verify(metamath) > 0).equalsTo(true);
    
  });
});

function assertThat(x) {
  return {
    equalsTo(y) {
      Assert.deepEqual(x, y);
    }
  }
}
