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

const moo = require("moo");

const lexicon = {
  comment: { match: /\$\([\s]+(?:(?!\$\))[\s\S])*\$\)/, lineBreaks: true },
  lfile: "$[",
  rfile: "$]",
  v: "$v",
  d: "$d",
  c: "$c",
  f: "$f",
  a: "$a",
  e: "$e",
  p: "$p",
  proof: "$=",
  dot: "$.",
  // question: "?",
  lscope: "${",
  rscope: "$}",
  // lparen: "(",
  // rparen: ")",
  ws: { match: /[\s]+/, lineBreaks: true },
  sequence: /[!-#%-~\?]+/,
  // letter_or_digit: /[A-Za-z0-9]/,
  // symbol: /[!-#%-~]+/,
};

const lexer = moo.compile(lexicon);

module.exports = {
  lexicon: lexicon,
  lexer: lexer,
};
