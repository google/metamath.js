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

  it("helloworld", () => {    
    const grammar = compileGrammar(`
      database -> outermost_scope_stmt:*
      outermost_scope_stmt -> include_stmt | constant_stmt | stmt

      # File inclusion command; process file as a database.
      # Databases should NOT have a comment in the filename.
      include_stmt -> "$[" filename "$]"

      # Constant symbols declaration.
      constant_stmt -> "$c" constant:+ "$."

      # A normal statement can occur in any scope.
      stmt -> block | 
              variable_stmt | 
              disjoint_stmt |
              hypothesis_stmt | 
              assert_stmt

      # A block. You can have 0 statements in a block.
      block -> "$\{" stmt:* "$\}"

      # Variable symbols declaration.
      variable_stmt -> "$v" variable:+ "$."

      # Disjoint variables. Simple disjoint statements have
      # 2 variables, i.e., "variable*" is empty for them.
      disjoint_stmt -> "$d" variable variable variable:* "$."

      hypothesis_stmt -> floating_stmt | essential_stmt

      # Floating (variable-type) hypothesis.
      floating_stmt -> LABEL "$f" typecode variable "$."

      # Essential (logical) hypothesis.
      essential_stmt -> LABEL "$e" typecode MATH_SYMBOL:* "$."

      assert_stmt -> axiom_stmt | provable_stmt

      # Axiomatic assertion.
      axiom_stmt -> LABEL "$a" typecode MATH_SYMBOL:* "$."

      # Provable assertion.
      provable_stmt -> LABEL "$p" typecode MATH_SYMBOL:* "$=" proof "$."

      # A proof. Proofs may be interspersed by comments.
      # If ’?’ is in a proof it’s an "incomplete" proof.
      proof -> uncompressed_proof | compressed_proof

      uncompressed_proof -> (LABEL | "?"):+
      compressed_proof -> "(" LABEL:* ")" COMPRESSED_PROOF_BLOCK+

      typecode -> constant

      filename -> MATH_SYMBOL 
      constant -> MATH_SYMBOL
      variable -> MATH_SYMBOL

      # lexicon

      PRINTABLE_SEQUENCE -> _PRINTABLE_CHARACTER:+

      MATH_SYMBOL -> (_PRINTABLE_CHARACTER):+

      # ASCII non-whitespace printable characters
      # _PRINTABLE-CHARACTER -> [#x21-#x7e]

      LABEL -> ( _LETTER_OR_DIGIT | "." | "-" | "_" ):+

      _LETTER_OR_DIGIT -> [A-Za-z0-9]

      COMPRESSED_PROOF_BLOCK -> ([A-Z] | "?"):+

      # Define whitespace between tokens. The -> SKIP
      # means that when whitespace is seen, it is
      # skipped and we simply read again.
      WHITESPACE -> (_WHITECHAR:+ | _COMMENT)

      # Comments. $( ... $) and do not nest.
      # _COMMENT -> "$(" WHITECHAR:+ (PRINTABLE_SEQUENCE):* _WHITECHAR+ "$)" _WHITECHAR

      # Whitespace
      _WHITECHAR -> [ \t\\n\v\f] {% id %}

      filename -> "helloworld"

    `);
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
    parser.feed("$[helloworld$]");
    assertThat(parser.results).equalsTo([[[[["$[", ["helloworld"], "$]"]]]]]);
  });
});


function assertThat(x) {
  return {
    equalsTo(y) {
      Assert.deepEqual(x, y);
    }
  }
}
