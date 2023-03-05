const Assert = require("assert");

describe("Compiler", () => {
  const {Transpiler, Compiler, Parser, Lexer} = require("../src/compiler.js");

  it("parser", () => {
    let result = new Parser().parse(`
      // hello world

      include "file.mm"

      axiom mp
        let wp: wff p
        let wq: wff q

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
        let wx: wff x
        let wy: wff y

        assert |- ~ p
        step 1) foo(): p
        step 2) bar(1): ~ /** this is a comment */ p
        step 3) tpl(0,1): term ( t + 0 )
      end
    `);
    
    assertThat(result).equalsTo([
      ["include", "file.mm"],
      ["axiom", "mp", [
        [
          ["let", ["wp", "wff", "p"]],
          ["let", ["wq", "wff", "q"]],
        ], [
          ["assume", ["maj", "|-", "p", "=>", "q"]],
          ["assume", ["min", "|-", "p"]],
        ],
        [
          ["disjoint", ["p", "q"]]
        ],
        ["assert", ["|-", "q"]],
      ]
      ],
      ["axiom", "we", [
        [],
        [],
        [],
        ["assert", ["|-", ""]],
      ]
      ],
      ["theorem", "theorem1", [
        [
          ["let", ["wx", "wff", "x"]],
          ["let", ["wy", "wff", "y"]],
        ],
        [],
        [],
        ["assert", ["|-", "~", "p"]]
      ],
       [
         ["1", "foo", [], ["p"]],
         ["2", "bar", ["1"], ["~", "p"]],
         ["3", "tpl", ["0", "1"], ["term", "(", "t", "+", "0", ")"]],
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
  let wp: wff p
  let wq: wff q
  assume foo: ( p -> q )
  assert wff ( p var q )
end

axiom w2
  let wp: wff p
  let wq: wff q
  assert wff ( p -> q )
end

theorem wnew
  let wp: wff p
  let wr: wff r
  let ws: wff s

  disjoint p r
  assert wff ( s -> ( r -> p ) )

  step 0) ws(): wff s
  step 1) wr(): wff r
  step 2) wp(): wff p
  step 3) w2(1,2): wff ( r -> p )
  step 4) w2(0,3): wff ( s -> ( r -> p ) )
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

    const {Verifier} = require("../src/descent.js");

    // Verifies that the proofs are valid.
    assertThat(new Verifier().verify(metamath)).equalsTo(1);

    const transpiler = new Transpiler().read(metamath);

    const source = transpiler.dump();
    
    const result = await new Compiler().compile(source);

    // Verifies that the proofs are valid.
    assertThat(new Verifier().verify(result)).equalsTo(1);
  });

  it("transpile", async () => {
    for (let file of ["tq.mm", "pq.mm", "miu.mm", "demo0.mm", "test.mm", "id.mm"]) {
      await transpile(`tests/${file}`);
    }
  });
});

describe("Transpile and Parse", () => {
  const {Verifier} = require("../src/descent.js");
  const {Transpiler, Compiler, Parser} = require("../src/compiler.js");

  it("transpile and parse", async () => {
    const fs = require("fs/promises");
    for (let src of ["demo0.mm", "pq.mm", "tq.mm", "test.mm"]) {
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
    }
  });

  it("testmod3", async function() {
    const program = await require("fs/promises").readFile(`tests/ql.mm`);
    const files = new Transpiler()
          .read(program.toString())
          .closure("testmod3");
    const typogram = Object.values(files).map(([, content]) => content).join("");
    const metamath = await new Compiler().compile(typogram);
    assertThat(new Verifier().verify(metamath)).equalsTo(49);
  });
  
  it("mpbirx", async function() {
    const program = await require("fs/promises").readFile(`tests/hol.mm`);
    const files = new Transpiler()
          .read(program.toString())
          .closure("mpbirx", true);
    const typogram = Object.values(files).map(([, content]) => content).join("");
    const metamath = await new Compiler().compile(typogram);
    assertThat(new Verifier().verify(metamath)).equalsTo(6);
  });

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
  
  it("mpbirx: transpile", async function() {
    const src = "hol.mm";
    const program = await require("fs/promises").readFile(`tests/${src}`);
    const files = new Transpiler()
          .read(program.toString())
          .closure("mpbirx", true);

    for (const [file, [deps, body]] of Object.entries(files)) {
      const header = deps.map((dep) => `include "${dep}.mm"`).join("\n");
      const content = `${header}\n${body}`;
      await write(`tests/${src}.dir`, `${file}.mm`, content);
    }
  });
  
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
  
  it("mpbirx: preprocess, compile and verify", async function() {
    const dir = "tests/hol.mm.dir";
    const file = "mpbirx.mm";

    const loader = (async (file) => {
      return require("fs/promises").readFile(file);
    });
    
    const metamath = await new Compiler(loader).compile(dir, file);

    assertThat(new Verifier().verify(metamath)).equalsTo(6);      
  });
  
  it("transpile, parse, compile and verify", async function() {
    this.timeout(50000); 

    // "ql.mm" passes, but we disable it because it takes a long time
    for (let src of ["demo0.mm", "pq.mm", "tq.mm", "test.mm", "trud.mm", "hol.mm"]) {
      const program = await require("fs/promises").readFile(`tests/${src}`);
      const theorems = new Verifier().verify(program.toString());
      assertThat(theorems > 0).equalsTo(true);
      const typogram = new Transpiler().read(program.toString()).dump();
      const metamath = await new Compiler().compile(typogram);
      assertThat(new Verifier().verify(metamath)).equalsTo(theorems);      
    }
  });
});

function assertThat(x) {
  return {
    equalsTo(y) {
      Assert.deepEqual(x, y);
    }
  }
}
