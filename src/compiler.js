const moo = require("moo");
const {MM, Compressor, Decompressor} = require("./metamath.js");

class Lexer {
  constructor() {
    const lexicon = {
      // /\/\*\*[^]*\*\//
      ["comment-expr"]: {match: new RegExp("/\\*[^*]*\\*+(?:[^/*][^*]*\\*+)*/"), lineBreaks: true},
      ["comment"]: {match: /\/\/.*\n/, lineBreaks: true},
      ["ws"]: {match: /[\s]+/, lineBreaks: true},
      ["_include_"]: "include",
      ["theorem"]: "theorem",
      ["axiom"]: "axiom",
      ["do"]: "do",
      ["let"]: "let",
      ["assume"]: "assume",
      ["disjoint"]: "disjoint",
      ["return"]: "return",
      ["("]: "(",
      [")"]: ")",
      ["{"]: "{",
      ["}"]: "}",
      ['"']: '"',
      ["'"]: "'",
      [":"]: ":",
      [","]: ",",
      [";"]: ";",
      ["@"]: "@",
      ["#"]: "#",
      ["\\"]: "\\",
      ["label"]: /[A-Za-z0-9-_.]+/,
      ["type"]: /[!#-&\*-:<-\[\]-_a-~]+/, // no ", ', ( ), ;, \, `, 
      ["char"]: /[!#-&\(-\[\]-~]+/, // no \ and " and '
      //["symbol"]: /[!-#%-\:<-~]+/, // no " ", "$", ";"
      //["quote"]: /\$[!-#%-~]+\$/,
      //["string"]: /\$(?:[!-#%-~]+(?:\s+[!-#%-~]+)*\s?)?\$/,
    };
    this.lexer = moo.compile(lexicon);
  }
  parse(code) {
    this.lexer.reset(code);
    return this;
  }
  next() {
    let next = this.lexer.next();
    if (!next) {
      this.head = undefined;
      return;
    }
    let {type, text} = next;
    this.head = [type, text];
    return this.head;
  }
  done() {
    assertThat(this.lexer.next()).equalsTo(undefined);
  }
  ws() {
    assertThat(this.next()[0]).equalsTo("ws");
  }
  eat(type, value) {
    assertThat(this.next()).equalsTo([type, value ? value : type]);
    return this;
  };
}

function assertThat(a) {
  return {
    equalsTo(b) {
      if (JSON.stringify(a) != JSON.stringify(b)) {
        throw new Error(`Assertion error: ${a} != ${b}.`);
      }
    }
  };
}

const labels = [
  // a subset of possible labels
  "label",
  // reserved keywords that can also be labels
  "_include_",
  "theorem",
  "axiom",
  "let",
  "assume",
  "disjoint",
  "return",
];

const symbols = [
  "(",
  ")",
  "{",
  "}",
  '"',
  ":",
  ",",
  //";",
  "@",
  "#",
  ...labels,
  "symbol",
];

const chars = [
  "(",
  ")",
  "{",
  "}",
  //'"',
  ":",
  ",",
  ";",
  "@",
  "#",
  "'",
  //...labels,
  "type",
  "char",
];

class Parser {
  constructor() {
    this.lexer = new Lexer();
    this.__id = 0;
  }
  id() {
    return this.__id++;
  }
  feed(code) {
    this.lexer.parse(code);
    this.lexer.next();
  }
  parse(code) {
    this.feed(code);
    return this.top();
  }
  eat(...types) {
    if (!this.lexer.head) {
      this.error();
    }
    for (let type of types) {
      if (this.lexer.head[0] == type) {
        const value = this.lexer.head[1];
        this.lexer.next();
        return value;
      }
    }
    this.error();
  }
  error() {
    const {head} = this.lexer;
    const {line, col, buffer} = this.lexer.lexer;
    //console.log(head);
    //console.log(this.lexer.lexer);
    // console.log(this.lexer.lexer.formatError());
    // throw new Error(this.lexer.lexer.formatError());
    throw new Error(`Unexpected token "${head[0]}":  "${head[1]}" on line ${line} column ${col}.`);
  }
  
  accepts(...types) {
    if (!this.lexer.head) {
      return false;
    }
    for (let type of types) {
      if (this.lexer.head[0] == type) {
        return true;
      }
    }
    return false;
  }

  escape2() {
    this.eat("\\");
    const ch = this.eat("\\", '"');
    return ch;
  }
  
  string() {
    const result = [];
    this.eat('"');
    do {
      if (this.accepts(...labels, ...chars)) {
        let s = this.eat(...labels, ...chars);
        while (this.accepts(...labels, ...chars)) {
          s += this.eat(...labels, ...chars);
        }
        result.push(s);
        continue;
      } else if (this.accepts("\\")) {
        //throw new Error("hi");
        result.push(this.escape2());
      } else if (this.accepts("ws")) {
        this.eat("ws");
      } else {
        break;
      }
    } while (true);
    this.eat('"');
    return result;
  }
  
  ws(optional = false) {
    const sp = ["ws", "comment", "comment-expr"];
    if (this.accepts(...sp)) {
      this.eat(...sp);
      // allows multiple whitespace types intermingled
      while (this.accepts(...sp)) {
        this.eat(...sp);
      }
    } else if (!optional) {
      this.error();
    }
  }

  param() {
    let first = this.type();
    this.ws(true);

    let label;
    let type;

    if (this.accepts(":")) {
      this.eat(":");
      this.ws();
      label = first;
      type = this.type();
      this.ws();
    } else {
      label = `${this.id()}`;
      type = first;
    }

    const varz = this.label();
    this.ws(true);
    return [label, type, varz];
  }
  
  head() {
    this.eat("(");
    this.ws(true);

    const f = [];

    // parameters
    while (this.accepts(...labels, "'")) {
      f.push(this.param());
      
      if (!this.accepts(",")) {
        break;
      }
      
      this.eat(",");
      this.ws(true);
    }

    this.eat(")");

    this.ws(true);
    
    return f;
  }

  assume() {
    this.eat("assume");
    this.ws();
    let label = "";
    if (this.accepts(...labels)) {
      label = this.label();
      this.ws(true);
      this.eat(":");
      this.ws(true);
    } else {
      label = `${this.id()}`;
    }
    const [type, str] = this.str();
    this.ws(true);
    this.eat(";");
    this.ws(true);
    return [label, type, str];
  }

  let() {
    this.eat("let");
    this.ws();
    const label = this.label();
    this.ws(true);
    this.eat(":");
    this.ws(true);
    const type = this.accepts(...labels) ? this.label() : this.symbol();
    this.ws();
    const name = this.label();
    this.ws(true);
    this.eat(";");
    this.ws(true);
    return [label, type, name];
  }
  
  body(extras = false) {

    const e = [];
    
    while (this.accepts("assume")) {
      const assume = this.assume();
      e.push(assume);
    };

    const d = [];
    while (this.accepts("disjoint")) {
      this.eat("disjoint");
      this.ws();
      const varzs = [];
      do {
        varzs.push(this.label());
        this.ws(true);
      } while (this.accepts(...labels));
      d.push(varzs);
      this.ws(true);
      this.eat(";");
      this.ws(true);
    };

    const l = [];
    
    while (this.accepts("let")) {
      l.push(this.let());
    };
    
    const proof = [];
    if (extras) {
      this.eat("do");
      this.ws(true);
      this.eat("{");
      this.ws(true);
      while (this.accepts(...labels, "@", "#")) {
        if (this.accepts("@")) {
          proof.push(`${this.eat("@")}${this.eat("label")}`);
        } else if (this.accepts("#")) {
          proof.push(this.eat("#"));
        } else {
          proof.push(this.label());
        }
        this.ws(true);
        this.eat(";");
        this.ws(true);
      }
      this.eat("}");
      this.ws(true);
      this.eat(";");
      this.ws(true);
    }

    const [type, str] = this.return();
    this.ws(true);
    return [e, d, l, [type, str], proof];
  }

  return() {
    this.eat("return");
    this.ws();
    const [type, str] = this.str();
    // const type = this.symbol();
    //this.ws();
    //const str = this.str();
    this.ws(true);
    this.eat(";");
    return [type, str];
  }

  str() {
    const type = this.symbol();
    this.ws();
    let str = [];
    if (this.accepts('"')) {
      str = this.string();
    } else {
      str.push(this.symbol());
    }
    return [type, str];
  }

  quote() {
    this.eat("'");
    const result = [];
    //console.log(this.lexer.head);
    //throw new Error("hi");
    do {
      if (this.accepts(...labels, "char", "type")) {
        result.push(this.eat(...labels, "char", "type"));
        continue;
      } else if (this.accepts("\\")) {
        result.push(this.escape2());
      } else {
        break;
      }
    } while (true);
    this.eat("'");
    return result.join("");
  }
  
  type() {
    if (this.accepts("label", "type")) {
      return this.eat("label", "type");
    }
    
    if (this.accepts("'")) {
      return this.quote();
    }
    
    this.error("Invalid type");
  }
  
  symbol() {
    if (this.accepts(...labels, "char", "type")) {
      return this.eat(...labels, "char", "type");
    }

    if (this.accepts("'")) {
      return this.quote();
    }

    this.error("Invalid symbol");
    
    return this.string().join("");
    
    if (this.accepts(...symbols)) {
      return this.eat(...symbols);
    }

    const quote = this.eat("quote");
    return quote.slice(1, quote.length - 1);
  }
  
  str2() {
    return this.string();
    if (this.accepts("quote", "string")) {
      const result = this.eat("quote", "string");
      const symbols = result.slice(1, result.length - 1);
      return symbols.split(/[\s]+/);
    }

    const str = [];
    while (this.accepts(...symbols)) {
      str.push(this.eat(...symbols));
      if (!this.accepts("ws")) {
        break;
      }
      this.ws();
    }
    return str;
  }

  axiom() {
    return this.func("axiom", false);
  }

  theorem() {
    return this.func("theorem", true);
  }
  
  func(type, extras) {
    this.eat(type);
    this.ws();
    let name = this.label();
    this.ws(true);
    const f  = this.head(extras);
    this.ws(true);
    this.eat("{");
    this.ws(true);
    const [e, d, l, [t, str], p] = this.body(extras);
    this.eat("}");
    this.ws(true);
    return [type, name, [
      f.map((p) => ["param", p]),
      l.map((v) => ["let", v]),
      e.map(([label, type, str]) => ["assume", [label, type, str]]),
      d.map((varz) => ["disjoint", varz]),
      ["assert", [t, str]],
    ], p];
  }
  
  args() {
    this.eat("(");
    this.ws(true);
    let args = [];
    if (this.accepts(...labels)) {
      args.push(this.label());
      this.ws(true);
    }
    while (this.accepts(",")) {
      this.eat(",");
      this.ws(true);
      args.push(this.label());
    }
    this.ws(true);
    this.eat(")");
    return args;
  }
  
  label() {
    let name = this.eat(...labels);
    while (this.accepts(...labels)) {
      name += this.eat(...labels);
    }
    return name;
  }
  
  include() {
    this.eat("_include_");
    this.ws();
    this.eat('"');
    const name = this.label();
    this.eat('"');
    this.ws(true);
    this.eat(";");
    this.ws();
    return ["include", name];
  }
    
  top() {
    let result = [];
    do {
      if (this.accepts("ws", "comment", "comment-expr")) {
        this.ws();
      } else if (this.accepts("axiom")) {
        result.push(this.axiom());
      } else if (this.accepts("theorem")) {
        result.push(this.theorem());
      } else if (this.accepts("_include_")) {
        result.push(this.include());
      } else if (!this.lexer.head) {
        continue;
      } else {
        this.error();
      }
    } while (this.lexer.head);
    return result;
  }
}

class Compiler {
  constructor(loader) {
    this.load = loader;
  }
  async preprocess(dir, file, shallow) {
    const queue = [file];

    const files = {};

    if (shallow) {
      const program = await this.load(`${dir}/${file}`);

      const parser = new Parser();
      const code = parser.parse(program.toString());
    
      files[file] = code;

      // Take all include statements that have never
      // been seen before and push them into the queue
      const include = code
            .filter(([type]) => type == "include")
            .map(([, name]) => name)
            .filter((name) => !files[name]);

      for (const file of include) {
        const program = await this.load(`${dir}/${file}`);
        const parser = new Parser();
        const code = parser.parse(program.toString());
        files[file] = code;
      }

      return files;
    }
    
    while (queue.length > 0) {
      const head = queue.shift();

      const program = await this.load(`${dir}/${head}`);

      const parser = new Parser();
      const code = parser.parse(program.toString());

      files[head] = code;

      // Take all include statements that have never
      // been seen before and push them into the queue
      const include = code
            .filter(([type]) => type == "include")
            .map(([, name]) => name)
            .filter((name) => !files[name]);

      queue.push(...include);
    }

    return files;
  }

  async compile(dirOrSource, file, shallow = false) {
    if (!file) {
      let parser = new Parser();
      let code = parser.parse(dirOrSource);
      return this.transpile(code);
    }
    const files = await this.preprocess(dirOrSource, file, shallow);
    const dump = Object.values(files)
          .flat()
          .filter(([type]) => type != "include");
    return this.transpile(dump);
  }

  transpile(code) {
    const consts = new Set();

    const statements = code.filter(([type]) => type != "include");
    
    for (let [type, label, [vars, dummies, assumes, disjoints, [, assert]], proof] of statements) {
      // All variable types are constants
      for (let type of vars.map(([, [label, type, name]]) => type)) {
        consts.add(type);
      }

      // All types in assertions are constants
      consts.add(assert[0]);

      const names = vars.map(([, [label, type, name]]) => name);

      // All symbols in logical hypothesis that aren't variables are constants
      //console.log(assumes);
      const logical = [...assumes]
            .map(([, [label, type, symbols]]) => [type, ...symbols])
            .map((symbols) => symbols.filter((symbol) => !names.includes(symbol)))
            .flat();
      //console.log(assumes);
      //console.log(logical);
      //throw new Error("hi");
      for (let symbol of logical) {
        consts.add(symbol);
      }
      // All symbols in assertions that aren't variables are constants
      const [, str] = assert;
      for (let symbol of str.filter((symbol) => !names.includes(symbol))) {
        consts.add(symbol);
        //console.log(symbol);
        //throw new Error("hi");
      }
    }

    //console.log(consts);
    //throw new Error("hi");

    let result = [];
    result.push(`$c ${[...consts].join(" ")} $.`);

    for (let [type, label, [vars, dummies, assumes, disjoints, [, assert]], proof] of statements) {

      const names = [...vars, ...dummies].map(([, [label, type, name]]) => name);

      const mandatory = new Set();

      //console.log();
      //throw new Error("hi");
      //assumes.map(([, [label, type, str]]) => str)
      //console.log();
      //console.log(assert.flat());
      //throw new Error("hi");
      for (const tok of [
        // ...assumes.map(([, [label, type, string]]) => string), assert
        ...assumes.map(([, [label, type, string]]) => [type, ...string]).flat(),
        ...assert.flat()
      ]) {
        //console.log(tok);
        //throw new Error("hi");
        //for (const tok of hyp) {
          
        if (names.includes(tok)) {
          mandatory.add(tok);
        } else if (!consts.has(tok)) {
          throw new Error(`Undeclared token: "${tok}" is neither a constant nor a variable.`);
        }
        //}
      }

      // console.log(mandatory);
      
      const types = [...vars, ...dummies].map(([, [label, type, name]]) => `  ${label} $f ${type} ${name} $.`);
      //console.log(assumes);
      //const logical = [...JSON.parse(JSON.stringify(assumes))]
      //      .map(([, assumption]) => [assumption.shift(), assumption.shift(), assumption])
      //      .map(([label, type, symbols]) => `  ${label} $e ${type} ${symbols.join(" ")} $.`);

      const logical = assumes.map(([assume, [label, type, str]]) => `  ${label} $e ${type} ${str.join(" ")} $.`);
      //console.log(logical);
      //throw new Error("hi");
      

      //console.log(assumes);
      //throw new Error("hi");
      //console.log(assumes);
      //throw new Error("hi");
      
      const dvis = disjoints.map(([, vars]) => `${vars.join(" ")}`);

      const d = disjoints.map(([, [a, b]]) => `  $d ${a} ${b} $.`).join("\n");
      //throw new Error();
      
      const v = names.length > 0 ? `  $v ${names.join(" ")} $.` : "";
      const f = types.length > 0 ? `${types.join("\n")}` : "";
      const e = logical.length > 0 ? `${logical.join("\n")}` : "";
      //const d = disjoints.length > 0 ? `  $d ${dvis.join(" ")} $.` : "";

      let p = "";

      if (proof) {
        let compress = false;
        const s = proof.map((label) => {
          if (label == "#") {
            compress = true;
            return -1;
          } else if (label.startsWith("@")) {
            return parseInt(label.substr(1));
          }
          return label;
        });

        if (!compress) {
          p = `$= ${proof.join(" ")} `;
        } else {
          const f = vars
                .filter(([, [, , name]]) => mandatory.has(name))
                .map(([letty, [label, type, name]]) => label);
          const e = [...JSON.parse(JSON.stringify(assumes))]
                .map(([, assumption]) => [assumption.shift(), assumption.shift(), assumption])
                .map(([label, type, symbols]) => label);
          const compressor = new Compressor([...f, ...e], s);
          const compressed = compressor.compress();
          
          p = `$= ( ${compressor.external().join(" ")} ) ${compressor.compress()} `;
        }
      }
      
      result.push(`
$\{
${v}
${f}
${e}
${d}
  ${label} $${type == "axiom" ? "a" : "p"} ${assert[0]} ${assert[1].join(" ")} ${type == "theorem" ? p : ""}$.
$\}`);
    }

    return result.join("\n");
  }
}

class Transpiler {
  read(program) {
    this.mm = this.parse(program);
    return this;
  }

  closure(label) {
    const files = this.split();
    //console.log(files);
    //throw new Error("hi");
    const queue = [label];

    const list = [];

    const result = {};
    
    while (queue.length > 0) {
      let head = queue.shift();
      if (list.includes(head)) {
        continue;
      }
      list.push(head);
      if (!files[head]) {
        console.log(head);
        throw new Error();
      }
      let [deps] = files[head];
      queue.push(...deps);
    }

    for (let file of list) {
      const [deps, content] = files[file];
      result[file] = [deps, content];
    }
    
    return result;
  }
  
  dump() {
    let result = [];
    for (const [label] of Object.entries(this.mm.labels).filter(([, [type]]) => type == "$a")) {
      const [, code] = this.axiom(label);
      result.push(code);
    }
    for (const [label] of Object.entries(this.mm.labels).filter(([, [type]]) => type == "$p")) {
      const [, code] = this.theorem(label);
      result.push(code);
    }
    return result.join("");
  }
  
  axiom(label) {
    const [, [d, f, e, [type, axiom]]] = this.mm.labels[label];

    let args = f.map(([type, name, label]) => {
      return `${label}: ${this.type(type)} ${name}`;
    }).join(", ");
    
    let assumptions = e.map(([seq, type, name]) => `  assume ${name}: ${this.type(type)} "${this.escape(seq.join(' '))}";`).join("\n");

    if (Object.entries(e).length > 0) {
      assumptions += "\n";
    }

    const result = `
axiom ${label}(${args}) {
${assumptions}
  return ${this.type(type)} "${this.escape(axiom.join(' '))}";
}
`;

    return [[], result];
  }

  escape(str) {
    //return str;
    return str.replaceAll('\\', `\\\\`).replaceAll('"', '\\"');
  }
  
  theorem(label) {
    // const deps = [];
    const [, [d, f, e, [type, theorem], ddummy, dummy], func, proof] = this.mm.labels[label];

    const labels = this.mm.labels;
    const dummies = Object
          .entries(dummy)
          .map(([name, label]) => [labels[label][1][0], name, label]);

    //let args = [...f, ...dummies]
    //    .map(([type, name, label]) => )
    //    .join("\n");

    //const varz = [];

    //for (const [type, name, label] of f) {
    //  varz.push(`  param ${label}: ${type} ${name}`);
    //}
    
    //for (const [type, name, label] of dummies) {
    //  varz.push(`  let ${label}: ${type} ${name}`);
    //}
    
    const args = f.map(([type, name, label]) => {
      //if (!type.match(/[A-Za-z]+/)) {
      //  // throw new Error(`Invalid type name: just letter allowed.`);
      //  return `${label}: '${this.escape(type)}' ${name}`;
      //}
      return `${label}: ${this.type(type)} ${name}`;
    }
    ).join(", ");
    
    const dlabels = dummies.map(([type, name, label]) => label);

    const local = [...f.map(([, , label]) => label),
                   ...e.map(([, , label]) => label)];

    //console.log(d);
    
    //console.log(ddummy);
    //throw new Error("hi");
    
    let steps = proof;
    if (proof[0] == "(") {
      const [, external, , compressed] = proof;
      steps = new Decompressor().decompress(local, external, compressed);
    }

    const deps = [...new Set(steps)]
          .filter((step) => !local.includes(step))
          .filter((step) => !dlabels.includes(step))
          .filter((step) => typeof step != "number");

    let conds = "";
    
    let assumptions = e.map(([seq, type, name]) => `  assume ${name}: ${type} "${this.escape(seq.join(' '))}";`).join("\n");

    if (Object.entries(e).length > 0) {
      assumptions += "\n";
    }
    
    let diff = [];
    for (let [x, y] of d) {
      diff.push(`  disjoint ${x} ${y};`);
    }
    
    for (let [x, y] of ddummy) {
      diff.push(`  disjoint ${x} ${y};`);
    }

    // console.log();
    //throw new Error("hi");
    
    const body = steps.map((step, i) => {
      const call = typeof step == "number" ? (step == -1 ? `#` : `@${step}`) : `${step}`;
      return `    ${call};`;
    }).join("\n");

    const l = dummies.map(([type, name, label]) => `  let ${label}: ${this.escape(type)} ${name};`).join("\n");
    
    const code = `
theorem ${label}(${args}) {
${assumptions}
${d.length > 0 ? diff.join("\n") : ""}

${l}

  do {
${body}
  };

  return ${this.type(type)} "${this.escape(theorem.join(' '))}";
}
`;

    return [deps, code];
  }

  type(type) {
    if (type.match(/[!#-&\*-:<-\[\]-_a-~]+/)) {
      return type;
    }
    return `'${this.escape(type)}'`;
  }
  
  parse(program) {
    const mm = new MM();
    mm.push();
    
    const {parse} = require("../src/descent.js");
    parse(program.toString(), {
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

    return mm;
  }
  
  split(program) {
    const result = {};
    
    for (const [label, value] of Object.entries(this.mm.labels)) {
      const [stmt] = value;
      if (stmt == "$e" || stmt == "$f" || label == "$c" || label == "$v") {
        continue;
      } else  if (stmt == "$a") {
        result[label] = this.axiom(label);
      } else if (stmt == "$p") {
        result[label] = this.theorem(label);
      } else {
        throw new Error(`Unknown statement type ${stmt}.`);
      }
    }
    return result;
  }
}

module.exports = {
  Lexer: Lexer,
  Parser: Parser,
  Compiler: Compiler,
  Transpiler: Transpiler,
};
