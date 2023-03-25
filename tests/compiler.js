const Assert = require("assert");
const {Verifier} = require("../src/descent.js");

describe("Compiler", () => {
  const {Transpiler, Compiler, Parser, Lexer} = require("../src/compiler.js");

  it("parser", () => {
    let result = new Parser().parse(`
      // hello world

      include "file.mm"

      axiom mp
        param wp: wff p
        param wq: wff q

        // logical hypothesis
        assume maj: |- p => q
        assume min: |- p

        // disjoint variables
        disjoint p q
        
        assert |- q
      end

      axiom we
        // empty symbols allowed
        assert |-
      end

      theorem theorem1
        // variable declarations
        param wx: wff x
        param wy: wff y

        assert |- ~ p

        proof

          foo
          bar
          tpl
          #
          @4

      end
    `);
    
    assertThat(result).equalsTo([
      ["include", "file.mm"],
      ["axiom", "mp", [
        [
          // arguments
          ["param", ["wp", "wff", "p"]],
          ["param", ["wq", "wff", "q"]],
        ], [
          // local variables
        ],
        [
          // assumptions
          ["assume", ["maj", "|-", "p", "=>", "q"]],
          ["assume", ["min", "|-", "p"]],
        ],
        [
          // disjoint requirements
          ["disjoint", ["p", "q"]]
        ],
        // assertion
        ["assert", ["|-", "q"]],
      ]
      ],
      ["axiom", "we", [
        [],
        [],
        [],
        [],
        ["assert", ["|-", ""]],
      ]
      ],
      ["theorem", "theorem1", [
        [
          ["param", ["wx", "wff", "x"]],
          ["param", ["wy", "wff", "y"]],
        ],
        [],
        [],
        [],
        ["assert", ["|-", "~", "p"]]
      ],
       [
         "foo",
         "bar",
         "tpl",
         "#",
         "@4",
       ]]
    ]);
  });
  
  it("lexer: const", async () => {
    let lexer = new Lexer();
    lexer.parse(`
      const => + -
    `);
    lexer.ws("ws");
    lexer.eat("label", "const");
    lexer.ws();
    lexer.eat("sequence", "=>");
    lexer.ws();
    lexer.eat("sequence", "+");
    lexer.ws();
    lexer.eat("label", "-");
    lexer.ws();
    lexer.done();
  });
  
  it("lexer: let", async () => {
    let lexer = new Lexer();
    lexer.parse(`
      let wff x y
    `);
    lexer.ws();
    lexer.eat("let");
    lexer.ws();
    lexer.eat("label", "wff");
    lexer.ws();
    lexer.eat("label", "x");
    lexer.ws();
    lexer.eat("label", "y");
    lexer.ws();
    lexer.done();
  });
  
  it("lexer: theorem", async () => {
    let lexer = new Lexer();
    lexer.parse(`
      theorem foobar
        let wff p
      proof
      end
    `);

    lexer.ws();
    lexer.eat("theorem");
    lexer.ws();
    lexer.eat("label", "foobar");
    lexer.ws();
    lexer.eat("let");
    lexer.ws();
    lexer.eat("label", "wff");
    lexer.ws();
    lexer.eat("label", "p");
    lexer.ws();
    lexer.eat("proof");
    lexer.ws();
    lexer.eat("end");
    lexer.ws();
    lexer.done();
  });
  
  it("lexer: axiom", async () => {
    let lexer = new Lexer();

    lexer.parse(`
      axiom foobar
        let wff p
        let wff q
        assume p => q
        assume |- p
        assert |- q
      end
    `);

    lexer.ws();
    assertThat(lexer.next()).equalsTo(["axiom", "axiom"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "foobar"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["let", "let"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "wff"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "p"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["let", "let"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "wff"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "q"]);
    // assertThat(next()).equalsTo([":", ":"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["assume", "assume"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "p"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["sequence", "=>"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "q"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["assume", "assume"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["sequence", "|-"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "p"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["assert", "assert"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["sequence", "|-"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["label", "q"]);
    lexer.ws();
    assertThat(lexer.next()).equalsTo(["end", "end"]);
    lexer.ws();
    lexer.done();
  });
});

describe("Transpiler", () => {
  const moo = require("moo");
  const fs = require("fs/promises");

  async function transpile(src) {
    const program = await fs.readFile(src);
    const files = await new Transpiler().read(program).split();

    const dir = `${src}.dir`;

    // Creates a directory if one doesn't exist
    try {
      const file = await fs.stat(dir);
      if (!file.isDirectory()) {
        throw new Error("hi");
      }
    } catch (e) {
      await fs.mkdir(dir);
    }

    for (let [name, [deps, content]] of Object.entries(files)) {
      const header = deps.map((dep) => `include "${dep}.mm"`).join("\n") + "\n";
      await fs.writeFile(`${dir}/${name}.mm`, `${deps.length > 0 ? header : ""}${content}`);
    }
  }

  it("empty", async () => {
    const transpiler = new Transpiler();
    const result = transpiler.read(``).split();
    assertThat(result).equalsTo({});
  });

  const {Transpiler, Compiler} = require("../src/compiler.js");
  
  it("transpile", async () => {
    const metamath = `
      $c ( ) -> wff : var $.
      $v p q r s $.
      wp $f wff p $.
      wq $f wff q $.
      wr $f wff r $.
      ws $f wff s $.
      $d p r $.
      $\{
        foo $e ( p -> q ) $.
        w0 $a wff ( p var q ) $.
      $\}
      w2 $a wff ( p -> q ) $.
      wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.
    `;
    
    assertThat(new Transpiler().read(metamath).dump()).equalsTo(`
axiom w0
  param wp: wff p
  param wq: wff q
  assume foo: ( p -> q )
  assert wff ( p var q )
end

axiom w2
  param wp: wff p
  param wq: wff q
  assert wff ( p -> q )
end

theorem wnew
  param wp: wff p
  param wr: wff r
  param ws: wff s

  disjoint p r
  assert wff ( s -> ( r -> p ) )

  proof
    ws
    wr
    wp
    w2
    w2
end
`);

  });
  
  it("compile", async () => {
    const metamath = `
      $c ( ) -> wff : var $.
      $v p q r s $.
      wp $f wff p $.
      wq $f wff q $.
      wr $f wff r $.
      ws $f wff s $.
      $d p r $.
      $\{
        bar $f var p $.
        foo $e p : q $.
        w0 $a wff ( p -> q ) $.
      $\}
      w2 $a wff ( p -> q ) $.
      wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.
    `;
    const transpiler = new Transpiler().read(metamath);

    const source = transpiler.dump();

    const result = await new Compiler().compile(source);
    assertThat(result).equalsTo(
`$c wff var : ( -> ) $.

$\{
  $v q p $.
  wq $f wff q $.
  bar $f var p $.
  foo $e p : q $.

  w0 $a wff ( p -> q ) $.
$\}

$\{
  $v p q $.
  wp $f wff p $.
  wq $f wff q $.


  w2 $a wff ( p -> q ) $.
$\}

$\{
  $v p r s $.
  wp $f wff p $.
  wr $f wff r $.
  ws $f wff s $.

  $d p r $.
  wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.
$\}`);

  });
  
  it("transpile, compile and verify idALT", async () => {
    const program = await fs.readFile("tests/idalt.mm");
    const transpiler = new Transpiler().read(program.toString());
    const source = transpiler.dump();
    const result = await new Compiler().compile(source);
    assertThat(new Verifier().verify(result)).equalsTo(1);
  });
  
  it("verify", async () => {
    const metamath = `
      $c ( ) -> wff $.
      $v p q r s $.
      wp $f wff p $.
      wq $f wff q $.
      wr $f wff r $.
      ws $f wff s $.
      w2 $a wff ( p -> q ) $.
      wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.
    `;

    // Verifies that the proofs are valid.
    assertThat(new Verifier().verify(metamath)).equalsTo(1);

    const transpiler = new Transpiler().read(metamath);

    const source = transpiler.dump();
    
    const result = await new Compiler().compile(source);

    // Verifies that the proofs are valid.
    assertThat(new Verifier().verify(result)).equalsTo(1);
  });

  for (let file of [
    "tq.mm",
    "pq.mm",
    "miu.mm",
    "demo0.mm",
    "test.mm",
    "id.mm",
    "trud.mm",
    "hol.mm",
    "ql.mm",
    // Transpiling Set.mm takes too long to do on a regular basis 
    // "set.mm",
  ]) {
    it(`Transpile ${file}`, async function () {
      this.timeout(50000);
      await transpile(`tests/${file}`);
    });
  }
});

describe("Transpile and Parse", () => {
  const {Verifier} = require("../src/descent.js");
  const {Transpiler, Compiler, Parser} = require("../src/compiler.js");

  for (let src of ["tq.mm", "pq.mm", "miu.mm", "demo0.mm", "test.mm", "id.mm", "trud.mm"]) {
    it(`Transpile and parse: ${src}`, async () => {
      const fs = require("fs/promises");
      const program = await fs.readFile(`tests/${src}`);
      const files = await new Transpiler().read(program).split();
      for (let [name, [deps, content]] of Object.entries(files)) {
        let parser = new Parser();
        try {
          parser.parse(content);
        } catch (e) {
          console.log(`Error parsing ${name} of ${src}.`);
          throw e;
        }
      }
    });
  }

  for (const [file, label, expects] of [
    ["hol.mm", "mpbirx", 6],
    ["hol.mm", "cl", 39],
    ["ql.mm", "testmod3", 49],
    // 2p2e4 passes but is disabled becaused processing set.mm takes 30 secs
    // ["set.mm", "2p2e4", 796],
  ]) {
    it(`Transpile, compile and verify: ${file} ${label}`, async function() {
      this.timeout(50000);
      const program = await require("fs/promises").readFile(`tests/${file}`);
      const files = new Transpiler()
            .read(program.toString())
            .closure(label, true);
      const typogram = Object.values(files).map(([, content]) => content).join("");
      const metamath = await new Compiler().compile(typogram);
      assertThat(new Verifier().verify(metamath)).equalsTo(expects);
    });
  }
  
  async function write(dir, file, content) {
    const fs = require("fs/promises");

    // Creates a directory if one doesn't exist
    try {
      const file = await fs.stat(dir);
      if (!file.isDirectory()) {
        throw new Error("hi");
      }
    } catch (e) {
      await fs.mkdir(dir);
    }

    await fs.writeFile(`${dir}/${file}`, content);
  }

  for (const [src, label] of [
    ["hol.mm", "mpbirx"],
    ["hol.mm", "cl"],
  ]) {
    it(`Transpile theorem: ${src}.dir/${label}.mm`, async function() {
      const program = await require("fs/promises").readFile(`tests/${src}`);
      const [deps, body] = new Transpiler()
            .read(program.toString())
            .theorem(label, true);

      const header = deps.map((dep) => `include "${dep}.mm"`).join("\n");
      const content = `${header}\n${body}`;
      await write(`tests/${src}.dir`, `${label}.mm`, content);

      const metamath = await new Compiler().compile(body);
      // console.log(metamath);
    });
  }

  it("compile() empty string", async () => {
    assertThat(await new Compiler().compile(``))
      .equalsTo("$c  $.");
  });

  it("compile() ignores pre-processing directives", async () => {
    assertThat(await new Compiler().compile(`
      include "file.mm"
    `)).equalsTo("$c  $.");
  });

  it("$d: hol.mm / cl", async function() {
    const src = "hol.mm";
    const label = "cl";
    const program = await require("fs/promises").readFile(`tests/${src}`);
    const [deps, content] = new Transpiler()
          .read(program.toString())
          .theorem(label);
    assertThat(await new Compiler().compile(content)).
      equalsTo(`$c type var term |- : [ = ] |= T. ( \\ . ) $.

$\{
  $v al be x A B C y $.
  hal $f type al $.
  hbe $f type be $.
  vx $f var x $.
  ta $f term A $.
  tb $f term B $.
  tc $f term C $.
  vy $f var y $.
  cl.1 $e |- A : be $.
  cl.2 $e |- C : al $.
  cl.3 $e |- [ x : al = C ] |= [ A = B ] $.
  $d B x $.
  $d C x $.
  $d al x $.
  $d A y $.
  $d x y $.
  $d B y $.
  $d C y $.
  $d al y $.
  cl $p |- T. |= [ ( \\ x : al . A C ) = B ] $= ( vy tv ke kbr eqtypi wv ax-17 clf ) ABCJDEFGHIABCEAJKZBDEACKFLMGINAJOZPAACFRHSPQ $.
$\}`);;
  });

  it("Compress proof of cl", async function() {
    const src = "hol.mm";
    const label = "cl";
    const program = await require("fs/promises").readFile(`tests/${src}`);
    const files = new Transpiler()
          .read(program.toString())
          .closure(label);

    const dump = Object
          .values(files)
          .map(([deps, content]) => content)
          .join("");
    
    const metamath = await new Compiler().compile(dump);

    const {process} = require("../src/descent.js");
    const mm = process(metamath);
    const [, [d, f, e, rule], verifier, proof] = mm.labels[label];
  });
  
  it("Verify the correspondence: hol.mm / cl", async function() {
    const src = "hol.mm";
    const label = "cl";
    const program = await require("fs/promises").readFile(`tests/${src}`);
    const files = new Transpiler()
          .read(program.toString())
          .closure(label, true);

    const dump = Object
          .values(files)
          .map(([deps, content]) => content)
          .join("");
    
    const metamath = await new Compiler().compile(dump);

    const {process} = require("../src/descent.js");

    // process the original content
    const mm1 = process(program.toString());
    const [, [d1, f1, e1, rule1], verifier1, proof1] = mm1.labels[label];

    // process the transpiled and compiled content
    const mm2 = process(metamath);
    const [, [d2, f2, e2, rule2], verifier2, proof2] = mm2.labels[label];

    assertThat(mm1.labels["tv"]).equalsTo(mm2.labels["tv"]);

    // Asserts that the assertion is the same across both programs.
    
    assertThat(rule1).equalsTo(rule2);
    assertThat(d1).equalsTo(d2);
    assertThat(f1).equalsTo(f2);
    assertThat(e1).equalsTo(e2);
    const [, local1, , compressed1] = proof1;
    const [, local2, , compressed2] = proof2;

    assertThat(local1).equalsTo(local2);
    assertThat(compressed1).equalsTo(compressed2);
    
    assertThat(proof1.decompress()).equalsTo(proof2.decompress());
    assertThat(proof1.explode()).equalsTo(proof2.explode());
  });
  
  for (let [src, label] of [
    ["hol.mm", "wal"],
    ["hol.mm", "cl"],
    ["hol.mm", "mpbirx"],
    // This takes too long, so we avoid running it every time
    // ["set.mm", "2p2e4"],
  ]) {
    it(`Transpile the closure: ${label}`, async function() {
      this.timeout(50000);
      // const src = "hol.mm";
      const program = await require("fs/promises").readFile(`tests/${src}`);
      const files = new Transpiler()
            .read(program.toString())
            .closure(label);
    
      for (const [file, [deps, body]] of Object.entries(files)) {
        const header = deps.map((dep) => `include "${dep}.mm"`).join("\n");
        const content = `${header}\n${body}`;
        await write(`tests/${src}.dir`, `${file}.mm`, content);
      }
    });
  }
    
  it("mpbirx: preprocess", async function() {
    const dir = "tests/hol.mm.dir";
    const file = "mpbirx.mm";

    const loader = (async (file) => {
      return require("fs/promises").readFile(file);
    });
    
    const files = await new Compiler(loader).preprocess(dir, file);

    // The result of preprocessing the file lead to
    // fetching all of these other files
    assertThat(Object.keys(files)).equalsTo([
      'mpbirx.mm',
      'hb.mm',
      'ax-cb2.mm',
      'eqcomx.mm',
      'ax-eqmp.mm',
      'ke.mm',
      'kc.mm',
      'ax-cb1.mm',
      'ax-refl.mm',
      'a1i.mm',
      'ht.mm',
      'weq.mm',
      'ax-ceq.mm',
      'syl2anc.mm',
      'wc.mm',
      'kt.mm',
      'ax-trud.mm',
      'syl.mm',
      'kct.mm',
      'jca.mm',
      'ax-syl.mm',
      'ax-jca.mm'
    ]);
  });
  
  for (let [dir, file, label, s, d] of [
    ["tests/hol.mm.dir", "mpbirx.mm", "mpbirx", [16, 5], [6, 25]],
  ]) {
    it(`Compile and verify: ${file}`, async function() {
      let deps = 0;
      const loader = (async (file) => {
        deps++;
        return require("fs/promises").readFile(file);
      });

      // Shallow proof
      const shallow = await new Compiler(loader).compile(dir, file, true);
      assertThat(new Verifier().verify(shallow, label).length).equalsTo(s[0]);
      // Loads only 5 files.
      assertThat(deps).equalsTo(s[1]);

      // Deep proof
      deps = 0;
      const deep = await new Compiler(loader).compile(dir, file, false);
      assertThat(new Verifier().verify(deep)).equalsTo(d[0]);
      // Loads the transitive dependency, 25 files.
      assertThat(deps).equalsTo(d[1]);
    });
  }

  // "ql.mm" passes, but we disable it because it takes a long time
  for (let src of [
    "demo0.mm",
    "pq.mm",
    "tq.mm",
    "test.mm",
    //"ql.mm",
    "trud.mm",
    "hol.mm"
  ]) {
    it(`Transpile, dump, parse, compile and verify all of: ${src}`, async function() {
      this.timeout(50000); 
      const program = await require("fs/promises").readFile(`tests/${src}`);
      const theorems = new Verifier().verify(program.toString());
      assertThat(theorems > 0).equalsTo(true);
      const typogram = new Transpiler().read(program.toString()).dump();
      const metamath = await new Compiler().compile(typogram);
      assertThat(new Verifier().verify(metamath)).equalsTo(theorems);
    });
  }

  it.skip("Empty Program", async () => {
    const metamath = await new Compiler().compile("");
    assertThat(new Verifier().verify(metamath)).equalsTo(0);
  });

  it("S and K", async () => {
    const src = `
axiom term-k
  assert term K
end

axiom term-s
  assert term S
end

axiom term-c
  let call.1: term p
  let call.2: term q
  assert term p [ q ]
end

axiom ax-k
  let k.1: term x
  let k.2: term y
  assume k.1: |- K [ x ] [ y ]
  assert |- x
end

axiom ax-s
  let s.1: term x
  let s.2: term y
  let s.3: term z
  assume ax-s.1: |- S [ x ] [ y ] [ z ]
  assert |- x [ z ] [ y [ z ] ]
end

theorem sksk
  assume sksk.1: |- S [ K ] [ S ] [ K ]
  assert |- K
  proof

    term-k     /** wff K */

    term-s     /** wff S */
    term-k     /** wff K */
    term-c     /** wff S [ k ] */

      term-k     /** wff K */
      term-s     /** wff S */
      term-k     /** wff K */
      sksk.1   /** |- S [ K ] [ S ] [ K ] t */
      ax-s     /** |- K [ K ] [ S [ K ] ] t */

    ax-k     /** | K */
end

axiom df-true
  let t.1: term x
  let t.2: term y
  assume t.1: |- T [ x ] [ y ] 
  assert |- K [ x ] [ y ]
end

axiom df-false
  let t.1: term x
  let t.2: term y
  assume t.1: |- F [ x ] [ y ] 
  assert |- S [ K ] [ x ] [ y ]
end

theorem true
  let termx: term x
  let termy: term y
  assume true-e: |- T [ x ] [ y ] 
  assert |- x
  proof

    termx
    termy

      termx
      termy
      true-e
      df-true

    ax-k
end

theorem false
  let termx: term x
  let termy: term y
  assume false-e: |- F [ x ] [ y ] 
  assert |- y
  proof

    termy
      termx
      termy
    term-c

      term-k
      termx
      termy

        termx
        termy
        false-e
        df-false

      ax-s

    ax-k
end

axiom df-not
  let termx: term x
  assume e: |- NOT [ x ]
  assert |- S [ S [ I ] [ K [ F ] ] ] [ K [ T ] ] [ x ]
end

    `;
    
    const metamath = await new Compiler().compile(src);

    // console.log(metamath);
    
    assertThat(new Verifier().verify(metamath)).equalsTo(3);
    
  });
  
});

function assertThat(x) {
  return {
    equalsTo(y) {
      Assert.deepEqual(x, y);
    }
  }
}
