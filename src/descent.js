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

const {lexicon} = require("../src/lexer.js");
const {MM} = require("../src/metamath.js");
const moo = require("moo");

function *tokens(code) {
  const lexer = moo.compile(lexicon);
  lexer.reset(code);
  do {
    const next = lexer.next();
    if (!next) {
      return;
    }
    yield next;
  } while (true);
}

class Parser {
  constructor(handler) {
    this.handler = handler;
  }
  parse(tokens) {
    this.it = tokens;
    this.head = this.it.next();
    return this.program();
  }
  eat(type) {
    if (this.head.value.type != type) {
      throw new Error(`Expected ${type} got ${this.head.value.type}.`);
    }
    const token = this.head.value;
    this.head = this.it.next();
    return token.value;
  }
  accepts(type) {
    if (this.done()) {
      return false;
    }
    if (this.head.value.type == type) {
      return true;
    }
    return false;
  }
  done() {
    return this.head.done;
  }
  ws() {
    this.eat("ws");
  }
  comment() {
    this.eat("comment");
  }
  v() {
    const v = this.eat("v");
    this.space();
    const symbols = [];
    do {
      symbols.push(this.eat("sequence"));
      this.space();
    } while (this.accepts("sequence"));
    this.eat("dot");
    this.dispatch([v, symbols]);
  }
  c() {
    const c = this.eat("c");
    this.space();
    const symbols = [];
    while (this.accepts("sequence")) {
      symbols.push(this.eat("sequence"));
      this.space();
    };
    const dot = this.eat("dot");
    this.dispatch([c, symbols]);
  }
  dispatch(e) {
    if (this.handler) {
      this.handler.feed(e);
    }
  }
  d() {
    const d = this.eat("d");
    this.space();
    const symbols = [];
    do {
      symbols.push(this.eat("sequence"));
      this.space();
    } while (this.accepts("sequence"));
    this.eat("dot");
    this.dispatch([d, symbols]);
  }
  space(optional = false) {
    do {
      if (this.accepts("ws")) {
        this.ws();
      } else if (this.accepts("comment")) {
        this.comment();
      } else if (!optional) {
        throw new Error(`Excepted a ws or a comment`);
      }
    } while (this.accepts("ws") || this.accepts("comment"));
  }
  f(label) {
    const f = this.eat("f");
    this.space();
    const type = this.eat("sequence");
    this.space();
    const varz = this.eat("sequence");
    this.space();
    this.eat("dot");
    this.dispatch([label, f, type, varz]);
  }
  e(label) {
    const e = this.eat("e");
    this.space();
    const varz = this.eat("sequence");
    this.space();
    const sequence = [];
    do {
      sequence.push(this.eat("sequence"));
      this.space();
    } while (this.accepts("sequence"));
    this.eat("dot");
    this.dispatch([label, e, varz, sequence]);
  }
  a(label) {
    const a = this.eat("a");
    this.space();
    const type = this.eat("sequence");
    this.space();
    const sequence = [];
    while (this.accepts("sequence")) {
      sequence.push(this.eat("sequence"));
      this.space();
    };
    this.eat("dot");
    this.dispatch([label, a, type, sequence]);
  }
  value() {
    return this.head.value.value;
  }
  compressed() {
    const p1 = this.eat("sequence"); // (
    this.space();
    const local = [];
    while (this.value() != ")") {
      local.push(this.eat("sequence"));
      this.space();
    };
    const p2 = this.eat("sequence"); // )
    this.space();
    const integers = [];
    do {
      integers.push(this.eat("sequence"));
      this.space();
    } while (this.accepts("sequence"));
    return [p1, local, p2, integers.join("")];
  }
  uncompressed() {
    const proof = [];
    do {
      proof.push(this.eat("sequence"));
      this.space();
    } while (this.accepts("sequence"));
    return proof;
  }
  proof() {
    const proof = this.eat("proof");
    this.space();
    if (this.value() == "(") {
      return [proof, this.compressed()];
    } else {
      return [proof, this.uncompressed()];
    }
  }
  p(label) {
    const p = this.eat("p");
    this.space();
    const type = this.eat("sequence");
    this.space();
    const sequence = [];
    do {
      sequence.push(this.eat("sequence"));
      this.space();
    } while (this.accepts("sequence"));
    const [proof, steps] = this.proof();
    this.eat("dot");
    this.dispatch([label, p, type, sequence, proof, steps]);
  }
  label() {
    const label = this.eat("sequence");
    this.space();
    if (this.accepts("f")) {
      this.f(label);
    } else if (this.accepts("e")) {
      this.e(label);
    } else if (this.accepts("a")) {
      this.a(label);
    } else if (this.accepts("p")) {
      this.p(label);
    } else {
      this.error();
    }
  }
  error() {
    // console.log(this.head);
    const {line, col} = this.head.value;
    throw new Error(`Syntax error on line ${line} column ${col}: unexpected ${this.head.value.type} token.`);
  }
  block() {
    this.eat("lscope");
    this.dispatch("push");
    this.space();
    while (!this.accepts("rscope")) {
      this.statement();
      this.space(true);
    }
    this.eat("rscope");
    this.dispatch("pop");
  }
  file() {
    this.eat("lfile");
    this.space();
    this.eat("sequence");
    this.space();
    this.eat("rfile");
  }
  statement() {
    if (this.accepts("v")) {
      this.v();
    } else if (this.accepts("c")) {
      this.c();
    } else if (this.accepts("d")) {
      this.d();
    } else if (this.accepts("sequence")) {
      this.label();
    } else if (this.accepts("lscope")) {
      this.block();
    } else if (this.accepts("lfile")) {
      this.file();
    } else {
      this.error();
    }
  }
  program() {
    this.space(true);
    while (!this.done()) {
      this.statement();
      this.space(true);
    }
    return true;
  }
}

function parse(code, handler) {
  const parser = new Parser(handler);
  const stream = tokens(code);
  return parser.parse(stream);
}

function process(program) {
  const mm = new MM();
  mm.push();
  
  parse(program, {
    feed(statement) {
      if (statement == "push") {
        mm.push();
      } else if (statement == "pop") {
        mm.pop();
      } else {
        mm.feed([statement]);
      }
    }
  });

  //const [, , proof] = mm.labels[label];
  //return proof;
  return mm;
}

class Verifier {
  verify(program, label) {
    let proofs = 0;
    let mm = process(program);

    if (label) {
      const [, , proof] = mm.labels[label];
      return proof();
    }
    
    for (const [, [, , proof]] of Object.entries(mm.labels).filter(([, [type]]) => type == "$p")) {
      proof();
      proofs++;
    }
    return proofs;
  }
}

module.exports = {
  parse: parse,
  process: process,
  Verifier: Verifier,
};
