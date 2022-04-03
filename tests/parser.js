const Assert = require("assert");
const nearley = require("nearley");
const compile = require("nearley/lib/compile");
const generate = require("nearley/lib/generate");
const nearleyGrammar = require("nearley/lib/nearley-language-bootstrapped");

describe("Parser", () => {
  function compileGrammar(sourceCode) {
    // Parse the grammar source into an AST
    const grammarParser = new nearley.Parser(nearleyGrammar);
    grammarParser.feed(sourceCode);
    const grammarAst = grammarParser.results[0]; // TODO check for errors
      
    // Compile the AST into a set of rules
    const grammarInfoObject = compile(grammarAst, {});
    // Generate JavaScript code from the rules
    const grammarJs = generate(grammarInfoObject, "grammar");
      
    // Pretend this is a CommonJS environment to catch exports from the grammar.
    const module = { exports: {} };
    eval(grammarJs);

    return module.exports;
  }

  const grammar = compileGrammar(`
      database -> _ outermost_scope_stmt (__ outermost_scope_stmt):* _ {% ([ws1, stmt, list, ws2]) => 
        [stmt].concat(list.map(([ws, v]) => v)) 
      %}

      outermost_scope_stmt -> include_stmt {% id %} | 
                              constant_stmt {% id %} | 
                              stmt {% id %}

      # File inclusion command; process file as a database.
      # Databases should NOT have a comment in the filename.
      include_stmt -> "$[" filename "$]"

      # Constant symbols declaration.
      constant_stmt -> "$c" _ constant (__ constant):* _ "$." {% ([c, ws1, cons, list, ws2, d]) => 
        [c, [cons].concat(list.map(([ws, v]) => v)), d]
      %}

      # A normal statement can occur in any scope.
      stmt -> block {% id %} | 
              variable_stmt {% id %} | 
              disjoint_stmt {% id %} |
              hypothesis_stmt {% id %} | 
              assert_stmt {% id %}

      # A block. You can have 0 statements in a block.
      block -> "$\{" (__ stmt):* __ "$\}" {% ([b1, list, ws, b2]) => 
        [b1, list.map(([ws, v]) => v), b2] 
      %}

      # Variable symbols declaration.
      variable_stmt -> "$v" _ variable (__ variable):* _ "$." {% ([v, ws1, a, list, ws2, d]) => 
        [v, [a].concat(list.map(([ws, arg]) => arg)), d] 
      %}

      # Disjoint variables. Simple disjoint statements have
      # 2 variables, i.e., "variable*" is empty for them.
      disjoint_stmt -> "$d" variable variable variable:* "$."

      hypothesis_stmt -> floating_stmt | essential_stmt

      # Floating (variable-type) hypothesis.
      floating_stmt -> LABEL _ "$f" _ typecode _ variable _ "$." {% ([l, ws1, f, ws2, t, ws3, v, ws4, d]) => [l, f, t, v, d] %}

      # Essential (logical) hypothesis.
      essential_stmt -> LABEL __ "$e" __ typecode _ (__ MATH_SYMBOL):* __ "$." {% ([l, ws1, e, ws2, t, ws3, list, ws4, d]) => 
        [l, e, t, list.map(([ws, v]) => v), d] 
      %}

      assert_stmt -> axiom_stmt | provable_stmt

      # Axiomatic assertion.
      axiom_stmt -> LABEL _ "$a" _ typecode _ (__ MATH_SYMBOL):* _ "$." {% ([l, ws1, a, ws2, t, ws3, list, ws4, d]) => 
        [l, a, t, list.map(([ws, v]) => v), d] 
      %}

      # Provable assertion.
      provable_stmt -> LABEL "$p" typecode MATH_SYMBOL:* "$=" proof "$."

      # A proof. Proofs may be interspersed by comments.
      # If ’?’ is in a proof it’s an "incomplete" proof.
      proof -> uncompressed_proof | compressed_proof

      uncompressed_proof -> (LABEL | "?"):+
      compressed_proof -> "(" LABEL:* ")" COMPRESSED_PROOF_BLOCK+

      typecode -> constant

      filename -> MATH_SYMBOL {% id %}
      constant -> MATH_SYMBOL {% id %}
      variable -> MATH_SYMBOL {% id %}

      # lexicon

      PRINTABLE_SEQUENCE -> _PRINTABLE_CHARACTER:+

      # MATH_SYMBOL -> _PRINTABLE_CHARACTER:+ {% ([str]) => str.join("") %}
      MATH_SYMBOL -> [!-#%-~]:+ {% ([str]) => str.join("") %}

      # ASCII non-whitespace printable characters
      _PRINTABLE_CHARACTER -> [!-~]

      LABEL -> ( _LETTER_OR_DIGIT | "." | "-" | "_" ):+ {% ([str]) => str.join("") %}

      _LETTER_OR_DIGIT -> [A-Za-z0-9]

      COMPRESSED_PROOF_BLOCK -> ([A-Z] | "?"):+

      # Define whitespace between tokens. The -> SKIP
      # means that when whitespace is seen, it is
      # skipped and we simply read again.
      WHITESPACE -> (_WHITECHAR | _COMMENT)

      # Comments. $( ... $) and do not nest.
      _COMMENT -> "$(" _WHITECHAR:+ (PRINTABLE_SEQUENCE):* _WHITECHAR:+ "$)" _WHITECHAR

      # Whitespace
      _WHITECHAR -> [ \t\\n\v\f] {% id %}

      # Whitespace: _ is optional, __ is mandatory.
      _  -> WHITESPACE:* {% (d) => null %}
      __ -> WHITESPACE:+ {% (d) => null %}

  `);

  function parse(code) {
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
    parser.feed(code);
    return parser.results;
  }
  
  it("$[filename$]", () => {    
    assertThat(parse("$[filename$]"))
      .equalsTo([[["$[", "filename", "$]"]]]);
  });

  it("$( comment $)", () => {    
    assertThat(parse("$( comment $)"))
      .equalsTo([]);
  });

  it("$v a $.", () => {    
    assertThat(parse("$v a $."))
      .equalsTo([[["$v", ["a"], "$."]]]);
  });

  it("$v ab $.", () => {    
    assertThat(parse("$v ab $."))
      .equalsTo([[["$v", ["ab"], "$."]]]);
  });

  it("$v a b $.", () => {    
    assertThat(parse("$v a b $."))
      .equalsTo([[["$v", ["a", "b"], "$."]]]);
  });

  it("$v a b c $.", () => {    
    assertThat(parse("$v a b c $."))
      .equalsTo([[["$v", ["a", "b", "c"], "$."]]]);
  });

  it("$v t r s P Q $.", () => {    
    assertThat(parse("$v t r s P Q $."))
      .equalsTo([[["$v", ["t", "r", "s", "P", "Q",], "$."]]]);
  });

  it("$v a $. $v b $.", () => {    
    assertThat(parse("$v a $. $v b $."))
      .equalsTo([[
        ["$v", ["a"], "$."],
        ["$v", ["b"], "$."]
      ]]);
  });

  it("$c a $.", () => {    
    assertThat(parse("$c a $."))
      .equalsTo([[["$c", ["a"], "$."]]]);
  });

  it("$c a b $.", () => {    
    assertThat(parse("$c a b $."))
      .equalsTo([[["$c", ["a", "b"], "$."]]]);
  });

  it("$c 0 $.", () => {    
    assertThat(parse("$c 0 $."))
      .equalsTo([[["$c", ["0"], "$."]]]);
  });

  it("$c + $.", () => {    
    assertThat(parse("$c + $."))
      .equalsTo([[["$c", ["+"], "$."]]]);
  });

  it("$c = $.", () => {    
    assertThat(parse("$c = $."))
      .equalsTo([[["$c", ["="], "$."]]]);
  });

  it("$c -> $.", () => {    
    assertThat(parse("$c -> $."))
      .equalsTo([[["$c", ["->"], "$."]]]);
  });

  it("$c 0 + = -> ( ) term wff |- $.", () => {    
    assertThat(parse("$c 0 + = -> ( ) term wff |- $."))
      .equalsTo([[["$c", ["0", "+", "=", "->", "(", ")", "term", "wff", "|-"], "$."]]]);
  });

  it("tt $f term t $.", () => {    
    assertThat(parse("tt $f term t $."))
      .equalsTo([[[
        ["tt", "$f", ["term"], "t", "$."]
      ]]]);
  });

  it("weq $a wff t $.", () => {    
    assertThat(parse("weq $a wff t $."))
      .equalsTo([[[
        ["weq", "$a", ["wff"], ["t"], "$."]
      ]]]);
  });

  it("weq $a wff t u $.", () => {    
    assertThat(parse("weq $a wff t u $."))
      .equalsTo([[[
        ["weq", "$a", ["wff"], ["t", "u"], "$."]
      ]]]);
  });

  it("weq $a wff t = r $.", () => {    
    assertThat(parse("weq $a wff t = r $."))
      .equalsTo([[[
        ["weq", "$a", ["wff"], ["t", "=", "r"], "$."]
      ]]]);
  });

  it("wim $a wff ( P -> Q ) $.", () => {    
    assertThat(parse("wim $a wff ( P -> Q ) $."))
      .equalsTo([[[
        ["wim", "$a", ["wff"], ["(", "P", "->", "Q", ")"], "$."]
      ]]]);
  });
  
  it("a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.", () => {    
    assertThat(parse("a1 $a |- ( t = r -> ( t = s -> r = s ) ) $."))
      .equalsTo([[[
        ["a1", "$a", ["|-"], ["(", "t", "=", "r", "->", "(", "t", "=", "s", "->", "r", "=", "s", ")", ")"], "$."]
      ]]]);
  });

  it("a2 $a |- ( t + 0 ) = t $.", () => {    
    assertThat(parse("a2 $a |- ( t + 0 ) = t $."))
      .equalsTo([[[
        ["a2", "$a", ["|-"], ["(", "t", "+", "0", ")", "=", "t"], "$."]
      ]]]);
    });

  it("${ $}", () => {
    assertThat(parse("${ $}"))
      .equalsTo([[
        ["${", [], "$}"]
      ]]);
  });

  it("${  $}", () => {
    assertThat(parse("${  $}"))
      .equalsTo([[
        ["${", [], "$}"]
      ]]);
  });

  it("min $e |- P $.", () => {    
    assertThat(parse("min $e |- P $."))
      .equalsTo([[[
        ["min", "$e", ["|-"], ["P"], "$."]
      ]]]);
  });

  it("maj $e |- ( P -> Q ) $.", () => {    
    assertThat(parse("maj $e |- ( P -> Q ) $."))
      .equalsTo([[[
        ["maj", "$e", ["|-"], ["(", "P", "->", "Q", ")"], "$."]
      ]]]);
    });

  it("${ min $e |- P $. $}", () => {    
    assertThat(parse("${ min $e |- P $. $}"))
      .equalsTo([[
        ["${", [[
          ["min", "$e", ["|-"], ["P"], "$."]
        ]], "$}"]
      ]]);
    });

  it("${ min $e |- P $. maj $e |- ( P -> Q ) $. $}", () => {    
    assertThat(parse("${ min $e |- P $. maj $e |- ( P -> Q ) $. $}"))
      .equalsTo([[
        ["${", [
          [["min", "$e", ["|-"], ["P"], "$."]],
          [["maj", "$e", ["|-"], ["(", "P", "->", "Q", ")"], "$."]],          
        ], "$}"]
      ]]);
    });

});


function assertThat(x) {
  return {
    equalsTo(y) {
      Assert.deepEqual(x, y);
    }
  }
}
