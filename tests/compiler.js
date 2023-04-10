const Assert = require("assert");
const {Verifier} = require("../src/descent.js");

describe("Compiler", () => {
  const {Transpiler, Compiler, Parser, Lexer} = require("../src/compiler.js");

  it(`axiom foo() { return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    axiom foo() {
      return $|- bar$;
    }
    `);
    assertThat(result).equalsTo([
      ["axiom", "foo", [
        [],
        [],
        [],
        [],
        ["assert", ["|-", "bar"]],
      ], [
      ]]
    ]);
  });
  
  it(`axiom foo() { return $|- $; }`, () => {
    let result = new Parser().parse(`
    axiom foo() {
      return $|- $;
    }
    `);
    assertThat(result).equalsTo([
      ["axiom", "foo", [
        [],
        [],
        [],
        [],
        ["assert", ["|-", ""]],
      ], [
      ]]
    ]);
  });
  
  it(`axiom foo() { return $|- ;$; }`, () => {
    let result = new Parser().parse(`
    axiom foo() {
      return $|- ;$;
    }
    `);
    assertThat(result).equalsTo([
      ["axiom", "foo", [
        [],
        [],
        [],
        [],
        ["assert", ["|-", ";"]],
      ], [
      ]]
    ]);
  });

  it(`axiom foo() { return $term /\$; }`, () => {
    let result = new Parser().parse(`
    axiom foo() {
      return $term /\\$;
    }
    `);
    assertThat(result).equalsTo([
      ["axiom", "foo", [
        [],
        [],
        [],
        [],
        ["assert", ["term", "/\\"]],
      ], [
      ]]
    ]);
  });
    
  it(`include "foo.mm";`, () => {
    let result = new Parser().parse(`
     include "foo.mm";
    `);
    assertThat(result).equalsTo([
      ["include", "foo.mm"]
    ]);
  });

  it(`axiom foo(wff x) { return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    axiom foo(wff x) {
      return $|- bar$;
    }
    `);
    assertThat(result).equalsTo([
      ["axiom", "foo", [
        [["param", ["", "wff", "x"]]],
        [],
        [],
        [],
        ["assert", ["|-", "bar"]],
      ], [
      ]]
    ]);
  });
  
  it(`axiom foo(alet x) { return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    axiom foo(alet x) {
      return $|- bar$;
    }
    `);
    assertThat(result).equalsTo([
      ["axiom", "foo", [
        [["param", ["", "alet", "x"]]],
        [],
        [],
        [],
        ["assert", ["|-", "bar"]],
      ], [
      ]]
    ]);
  });
  
  it(`axiom foo($let$ x) { return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    axiom foo($let$ x) {
      return $|- bar$;
    }
    `);
    assertThat(result).equalsTo([
      ["axiom", "foo", [
        [["param", ["", "let", "x"]]],
        [],
        [],
        [],
        ["assert", ["|-", "bar"]],
      ], [
      ]]
    ]);
  });
  
  it(`axiom foo($|-$ x, $foo$ y, $\\"$ z) { return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    axiom foo($|-$ x, $foo$ y, $\\"$ z) {
      return $|- bar$;
    }
    `);
    assertThat(result).equalsTo([
      ["axiom", "foo", [
        [
          ["param", ["", '|-', "x"]],
          ["param", ["", 'foo', "y"]],
          ["param", ["", '\"', "z"]],
        ],
        [],
        [],
        [],
        ["assert", ["|-", "bar"]],
      ], [
      ]]
    ]);
  });
  
  it(`axiom foo(f1: wff x) { return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    axiom foo(f1: wff x) {
      return $|- bar$;
    }
    `);
    assertThat(result).equalsTo([
      ["axiom", "foo", [
        [["param", ["f1", "wff", "x"]]],
        [],
        [],
        [],
        ["assert", ["|-", "bar"]],
      ], [
      ]]
    ]);
  });
  
  it(`axiom foo(f1: $wff$ x) { return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    axiom foo(f1: wff x) {
      return $|- bar$;
    }
    `);
    assertThat(result).equalsTo([
      ["axiom", "foo", [
        [["param", ["f1", "wff", "x"]]],
        [],
        [],
        [],
        ["assert", ["|-", "bar"]],
      ], [
      ]]
    ]);
  });
  
  it(`axiom foo(wff, wffy) { return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    axiom foo(wff x, wff y) {
      assume $|- x$;
      disjoint x y;
      return $|- x [ y ]$;
    }
    `);

    assertThat(result).equalsTo([
      ["axiom", "foo", [
        [["param", ["", "wff", "x"]], ["param", ["", "wff", "y"]]],
        [],
        [["assume", ["", "|-", "x"]]],
        [["disjoint", ["x", "y"]]],
        ["assert", ["|-", "x", "[", "y", "]"]],
      ], [
      ]]
    ]);
  });
  
  it(`axiom foo() { return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    axiom foo() {
      assume maj: $|- x$;
      return $|- x [ y ]$;
    }
    `);

    assertThat(result).equalsTo([
      ["axiom", "foo", [
        [],
        [],
        [["assume", ["maj", "|-", "x"]]],
        [],
        ["assert", ["|-", "x", "[", "y", "]"]],
      ], [
      ]]
    ]);
  });
  
  it(`axiom foo() :$|- x$ { return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    axiom foo() {
      assume $|- x$;
      return $|- bar$;
    }
    `);
    assertThat(result).equalsTo([
      ["axiom", "foo", [
        [],
        [],
        [
          ["assume", ["", "|-", "x"]],
        ],
        [],
        ["assert", ["|-", "bar"]],
      ], [
      ]]
    ]);
  });
  
  it(`axiom foo() { assume $|- x$; assume $|- y$; return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    axiom foo() {
      assume $|- x$;
      assume $|- y$;
      return $|- bar$;
    }
    `);
    assertThat(result).equalsTo([
      ["axiom", "foo", [
        [],
        [],
        [
          ["assume", ["", "|-", "x"]],
          ["assume", ["", "|-", "y"]]
        ],
        [],
        ["assert", ["|-", "bar"]],
      ], [
      ]]
    ]);
  });

  it(`theorem foo() { return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    theorem foo() {
      do {
        hello;
        #;
        world;
        @2;
        let;
        return;
        letx;
        letreturn;
        theorem;
        axiom;
      };
      return $|- bar$;
    }
    `);
    assertThat(result).equalsTo([
      ["theorem", "foo", [
        [],
        [],
        [],
        [],
        ["assert", ["|-", "bar"]],
      ], [
        "hello", "#", "world", "@2",
        "let", "return", "letx", "letreturn", "theorem", "axiom"
      ]]
    ]);
  });

  it(`theorem foo() { return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    theorem foo() {
      let f1: wff p;
      let f2: $|-$ q;
      do {
      };
      return $|- bar$;
    }
    `);
    assertThat(result).equalsTo([
      ["theorem", "foo", [
        [],
        [
          ["let", ["f1", "wff", "p"]],
          ["let", ["f2", "|-", "q"]],
        ],
        [],
        [],
        ["assert", ["|-", "bar"]],
      ], [
      ]]
    ]);
  });

  it(`theorem foo() { let wp: wff p; return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    theorem foo() {
      let wp: wff p;
      let wq: wff q;
      do {
      };
      return $|- bar$;
    }
    `);
    assertThat(result).equalsTo([
      ["theorem", "foo", [
        [],
        [
          ["let", ["wp", "wff", "p"]],
          ["let", ["wq", "wff", "q"]],
        ],
        [],
        [],
        ["assert", ["|-", "bar"]],
      ], [
      ]]
    ]);
  });

  it(`theorem foo(f1: wff x, f2: wff y) { return $|- bar$; }`, () => {
    let result = new Parser().parse(`
    theorem foo(f1: wff x, f2: wff y) {
      assume e1: $|- x$;
      assume e2: $|- x -> y$;
      do {
      };
      return $|- bar$;
    }
    `);
    assertThat(result).equalsTo([
      ["theorem", "foo", [
        [
          ["param", ["f1", "wff", "x"]],
          ["param", ["f2", "wff", "y"]]
        ],
        [],
        [
          ["assume", ["e1", "|-", "x"]],
          ["assume", ["e2", "|-", "x", "->", "y"]],
        ],
        [],
        ["assert", ["|-", "bar"]],
      ],
      []]
    ]);
  });

  it("parser", () => {
    let result = new Parser().parse(`
      // hello world

      include "file.mm";

      axiom mp(wp: wff p, wq: wff q) {
        // logical hypothesis
        assume maj: $|- p => q$;
        assume min: $|- p$;

        // disjoint variables
        disjoint p q;
        
        return $|- q$;
      }

      axiom we() {
        // empty symbols allowed
        return $|- $;
      }

      theorem theorem1(wx: wff x, wy: wff y) {
        do {
          foo;
          bar;
          tpl;
          #;
          @4;
        };
        return $|- ~ p$;
      }
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
      ], []
      ],
      ["axiom", "we", [
        [],
        [],
        [],
        [],
        ["assert", ["|-", ""]],
      ], []
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


  it.skip("Symbols", async () => {
    let escape = (str) => str.replace(",", "$2C").replace(";", "$3B");
    let unescape = (str) => str.replace("$2C", ",").replace("$3B", ";");
    assertThat(escape("|-")).equalsTo("|-");
    assertThat(escape("+")).equalsTo("+");
    assertThat(escape("a;")).equalsTo("a$3B");
    assertThat(escape("a,")).equalsTo("a$2C");
    assertThat(unescape(escape("a;"))).equalsTo("a;");
    assertThat(unescape(escape("a,"))).equalsTo("a,");
    assertThat(String.fromCharCode(43)).equalsTo('+');
    assertThat(','.charCodeAt(0)).equalsTo(44);
    assertThat(';'.charCodeAt(0)).equalsTo(59);
    assertThat(String.fromCharCode(45)).equalsTo('-');
    let r = /[!-#%-+\--~]+/;
    assertThat("|-".match(r)[0]).equalsTo("|-");
    assertThat("+".match(r)[0]).equalsTo("+");
    assertThat("a$3B".match(r)[0]).equalsTo("a$3B");
    assertThat("a$2C".match(r)[0]).equalsTo("a$2C");
  });

  it("regex: symbols", async () => {
    const r = /\$[!-#%-~]+\$/;
    assertThat("$foobar$".match(r)[0]).equalsTo("$foobar$");
    assertThat('$"$'.match(r)[0]).equalsTo('$"$');
    assertThat('$/\$'.match(r)[0]).equalsTo('$/\$');
    assertThat('$/\\$'.match(r)[0]).equalsTo('$/\\$');
  });

  it("regex: strings", async () => {
    const r = /\$[!-#%-~]+(?:\s+[!-#%-~]+)*\$/;
    assertThat("$foobar$".match(r)[0]).equalsTo("$foobar$");
    assertThat('$"$'.match(r)[0]).equalsTo('$"$');
    assertThat('$/\$'.match(r)[0]).equalsTo('$/\$');
    assertThat(String.fromCharCode(36, 47, 92, 36)).equalsTo('$/\\$');
    assertThat('$/\\$'.match(r)[0]).equalsTo('$/\\$');
    assertThat(String.fromCharCode(36, 97, 32, 47, 92, 36)).equalsTo('$a /\\$');
    assertThat('$a /\\$'.match(r)[0]).equalsTo('$a /\\$');
  });
  
  it("quoted strings", async () => {
    assertThat(String.fromCharCode(34)).equalsTo('"');
    assertThat('"'.charCodeAt(0)).equalsTo(34); // "
    assertThat('\"'.length).equalsTo(1); 
    assertThat('\"'.charCodeAt(0)).equalsTo(34); // "
    assertThat('\\"'.length).equalsTo(2);
    assertThat('\\"'.charCodeAt(0)).equalsTo(92); // \
    assertThat('\\"'.charCodeAt(1)).equalsTo(34); // "
    assertThat('\\'.charCodeAt(0)).equalsTo(92); // \
    assertThat(String.fromCharCode(34, 97, 34)).equalsTo('"a"');
    const r = /"(?:[^"\\]|\\.)*"/;
    assertThat(String.fromCharCode(
      34, // "
      97, // a
      92, // \
      34, // "
      34  // "
    )).equalsTo('"a\\""');
    assertThat('"a\\""'.match(r)[0]).equalsTo(String.fromCharCode(34, 97, 92, 34, 34));
    assertThat(String.fromCharCode(
      34, // "
      97, // a
      92, // \
      34  // "
    )).equalsTo('"a\\"');
    assertThat('"a\\"'.match(r)).equalsTo(null); // no match
    assertThat(String.fromCharCode(
      34, // "
      97, // a
      34  // "
    )).equalsTo('"a"');
    assertThat('"').equalsTo('\"');
    assertThat(String.fromCharCode(
      34, // "
      47, // /
      92, // \
      34, // "
      34  // "
    )).equalsTo('"/\\""');
    assertThat('"/\\""'.match(r)[0]).equalsTo(String.fromCharCode(34, 47, 92, 34, 34));
    assertThat(String.fromCharCode(
      34, // "
      47, // /
      92, // \
      92, // \
      34  // "
    )).equalsTo('"/\\\\"');
    assertThat('"/\\\\"'.match(r)[0]).equalsTo(String.fromCharCode(34, 47, 92, 92, 34));
    
    return;
    assertThat("\"hello world\"".match(/"(?:[^"\\]|\\.)*"/)[0])
      .equalsTo('"hello world"');
    assertThat("\"hello \"foo\" world\"".match(/"(?:[^"\\]|\\.)*"/)[0])
      .equalsTo('"hello world"');
  });
  
  it(`lexer: strings`, async () => {
    new Lexer()
      .parse(`$/\\$  something else"`)
      .eat("string", '$/\\$');

    new Lexer()
      .parse(`$\\"$`)
      .eat("string", '$\\"$');

    new Lexer()
      .parse(`$/\\$`)
      .eat("string", '$/\\$')
      .done();

    new Lexer()
      .parse(`$term /\$`)
      .eat("string", '$term /\$')
      .done();

    new Lexer()
      .parse(`$term /\\$`)
      .eat("string", '$term /\\$')
      .done();

    new Lexer()
      .parse(`axiom foo($\"$ p)`)
      .eat("axiom", "axiom")
      .eat("ws", " ")
      .eat("label", "foo")
      .eat("(", "(")
      .eat("string", '$"$')
      .eat("ws", " ")
      .eat("label", "p")
      .next();

    new Lexer()
      .parse(`axiom foo($let$ x) { return $|- bar$; }`)
      .eat("axiom", "axiom")
      .eat("ws", " ")
      .eat("label", "foo")
      .eat("(", "(")
      .eat("string", '$let$')
      .eat("ws", " ")
    
    new Lexer()
      .parse(`axiom foo() { return $term /\\$; }`)
      .eat("axiom", "axiom")
      .eat("ws", " ")
      .eat("label", "foo")
      .eat("(", "(")
      .eat(")", ")")
      .eat("ws", " ")
      .eat("{", "{")
      .eat("ws", " ")
      .eat("return", "return")
      .eat("ws", " ")
      .eat("string", '$term /\\$')
      .eat(";", ";")
      .eat("ws", " ")
      .eat("}", "}")
      .done();

    new Lexer()
      .parse(`$a $  empty symbols"`)
      .eat("string", '$a $');

  });

  it("lexer: let", async () => {
    let lexer = new Lexer();
    lexer.parse(`
      let $let$: wff p;
    `);
    lexer.ws("ws");
    lexer.eat("let");
    lexer.ws("ws");
    lexer.eat("string", '$let$');
    lexer.eat(":", ":");
    lexer.ws("ws");
    lexer.eat("label", "wff");
    lexer.ws("ws");
    lexer.eat("label", "p");
    lexer.eat(";");
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
    lexer.eat("label", "proof");
    lexer.ws();
    lexer.eat("label", "end");
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
      const header = deps.map((dep) => `include "${dep}.mm";`).join("\n") + "\n";
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
      $c ( ) -> wff : var " $.
      $v p q r s t $.
      wp $f wff p $.
      wq $f wff q $.
      wr $f wff r $.
      ws $f wff s $.
      ww $f " t $.
      $d p r $.
      $\{
        foo $e ( p -> q ) $.
        w0 $a wff ( p var q ) $.
      $\}
      w2 $a wff ( p -> q ) $.
      wesc $a wff " t $.
      wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 w2 $.
    `;
    
    assertThat(new Transpiler().read(metamath).dump()).equalsTo(`
axiom w0(wp: $wff$ p, wq: $wff$ q) {
  assume foo: $( p -> q )$;

  return $wff ( p var q )$;
}

axiom w2(wp: $wff$ p, wq: $wff$ q) {

  return $wff ( p -> q )$;
}

axiom wesc(ww: $"$ t) {

  return $wff " t$;
}

theorem wnew(wp: $wff$ p, wr: $wff$ r, ws: $wff$ s) {

  disjoint p r;



  do {
    ws;
    wr;
    wp;
    w2;
    w2;
  };

  return $wff ( s -> ( r -> p ) )$;
}
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

    // console.log(source);
    
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

  for (let src of [
    "tq.mm",
    "pq.mm",
    "miu.mm",
    "demo0.mm",
    "test.mm",
    "id.mm",
    "trud.mm",
  ]) {
    it(`Transpile and parse: ${src}`, async () => {
      const fs = require("fs/promises");
      const program = await fs.readFile(`tests/${src}`);
      // console.log(program.toString());
      const files = await new Transpiler().read(program.toString()).split();
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
      //console.log(typogram);
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
      include "file.mm";
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
        const header = deps.map((dep) => `include "${dep}.mm";`).join("\n");
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

  it.skip("Compile and verify: tan.mm", async function() {
    const source = await require("fs/promises").readFile("tests/tan.mm");
    const shallow = await new Compiler().compile(source.toString());
    assertThat(new Verifier().verify(shallow)).equalsTo(0);
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
      //console.log(typogram);
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
axiom term-k() {
  return $term K$;
}

axiom term-s() {
  return $term S$;
}

axiom term-c() {
  let call.1: term p;
  let call.2: term q;
  return $term p [ q ]$;
}

// If Δ is a derivation ending in an expression of the form α((Kβ)γ)ι,
// then Δ followed by the term αβι is a derivation.
axiom ax-k(
  k.h: word head,
  k.1: term x,
  k.2: term y,
  k.t: word tail) {
  assume k.1: $|- head K [ x ] [ y ] tail$;
  return $|- head x tail$;
}

axiom word-c(word1: word w, word2: word c) {
  return $word w c$;
}

axiom word-null() {
  return $word $;
}

axiom word-t(word-t.0: term x) {
  return $word x$;
}

axiom word-l() {
  return $word [$;
}

axiom word-r() {
  return $word ]$;
}

// If Δ is a derivation ending in an expression of the form α(((Sβ)γ)δ)ι,
// then Δ followed by the term α((βδ)(γδ))ι is a derivation.
axiom ax-s(
  s.0: word head,
  s.1: term x,
  s.2: term y,
  s.3: term z,
  s.4: word tail) {
  assume ax-s.1: $|- head S [ x ] [ y ] [ z ] tail$;
  return $|- head x [ z ] [ y [ z ] ] tail$;
}

theorem s(s.1: term x, s.2: term y, s.3: term z) {
  assume s.e1: $|- S [ x ] [ y ] [ z ]$;
  do {
    word-null;

    s.1;
    s.2;
    s.3;

    word-null;

    s.e1;

    ax-s;
  };

  return $|- x [ z ] [ y [ z ] ]$;
}

theorem k(k.1: term x, k.2: term y) {
  assume k.e1: $|- K [ x ] [ y ]$;
  do {
    word-null;

    k.1;
    k.2;

    word-null;

    k.e1;

    ax-k;
  };
  return $|- x$;
}

axiom df-eq(
  eq.f0: word head,
  eq.f1: term x,
  eq.f2: term y,
  eq.f3: word tail) {
  assume eq.e0: $|- x = y$;
  assume eq.e1: $|- head x tail$;
  return $|- head y tail$;
}

axiom df-id() {
  return $|- I = S [ K ] [ K ]$;
}

axiom term-i() {
  return $term I$;
}

theorem id(
  id.fh: word head,
  id.f0: term x,
  id.ft: word tail) {
  assume id.e0: $|- head I [ x ] tail$;
  do {
    id.fh;
    id.f0;
    term-k;
    id.f0;
    term-c;
    id.ft;

      id.fh;
      term-k;
      term-k;
      id.f0;
      id.ft;

          id.fh;

          term-i;

          term-s;
          term-k;
          term-c;
          term-k;
          term-c;

          word-l;

          id.f0;
          word-t;
          word-c;

          word-r;
          word-c;

          id.ft;
          word-c;

          df-id;

          id.e0;

          df-eq;

      ax-s;

    ax-k;
  };

  return $|- head x tail$;
}

axiom term-f() {
  return $term F$;
}

axiom term-t() {
  return $term T$;
}

axiom df-true() {
  return $|- T = K$;
}

theorem true(
  true.h: word head,
  termx: term x,
  termy: term y,
  true.t: word tail) {
  assume true-e: $|- head T [ x ] [ y ] tail$;
  do {
    true.h;

    termx;

    termy;

    true.t;    

      true.h;

      term-t;

      term-k;

      word-l;

      termx;
      word-t;
      word-c;

      word-r;
      word-c;

      word-l;
      word-c;

      termy;
      word-t;
      word-c;

      word-r;
      word-c;

      true.t;
      word-c;

      df-true;

      true-e;

      df-eq;  
    
   ax-k;
  };
  return $|- head x tail$;
}

theorem sksk() {
  assume sksk.1: $|- S [ K ] [ S ] [ K ]$;
  do {
    term-k;     // wff K

    term-s;     // wff S
    term-k;     // wff K
    term-c;     // wff S [ k ]

      term-k;     // wff K
      term-s;     // wff S
      term-k;     // wff K

      sksk.1;   // |- S [ K ] [ S ] [ K ] t

      s;        // |- K [ K ] [ S [ K ] ] t

    k;     // | K
  };
  return $|- K$;
}

    `;
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
