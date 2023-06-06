/**
 *  Copyright 2022 Google LLC
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 **/

const nearley = require("nearley");
const compile = require("nearley/lib/compile");
const generate = require("nearley/lib/generate");
const nearleyGrammar = require("nearley/lib/nearley-language-bootstrapped");
const { lexer } = require("./lexer.js");

function compileGrammar(handler = false, sourceCode) {
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

const grammar = (handler) =>
  compileGrammar(handler, `
      @lexer lexer

      # Grammar rules...
      // ...`

function parse(code, handler = false) {
  const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar(handler)));
  parser.feed(code);
  return parser.results;
}

module.exports = {
  parse: parse,
  grammar: grammar,
};
