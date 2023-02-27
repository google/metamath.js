class Frame {
  constructor() {
    this.c = new Set();
    this.v = new Set();
    this.d = new Set();
    this.f = [];
    this.f_labels = {};
    this.e = [];
    this.e_labels = {};
  }
}
  
class Stack {
  constructor() {
    this.stack = [];
  }
    
  push() {
    const top = new Frame();
    this.stack.push(top);
    return top;
  }

  pop() {
    return this.stack.pop();
  }

  top() {
    return this.stack[this.stack.length - 1];
  }
    
  addC(tok) {
    const frame = this.top();
    
    if (frame.c.has(tok)) {
      throw new Error("const already declared in scope");
    }
    
    if (frame.v.has(tok)) {
      throw new Error("const already declared as a var in scope");
    }
    
    frame.c.add(tok);
  }

  addV(tok) {
    const frame = this.top();
    
    if (frame.v.has(tok)) {
      throw new Error("var already declared in scope");
    }
    
    if (frame.c.has(tok)) {
      throw new Error("var already declared as a const in scope");
    }
    
    frame.v.add(tok);
  }
  
  lookupV(tok) {
    for (const frame of [...this.stack].reverse()) {
      if (frame.v.has(tok)) {
        return true;
      }
    }
    return false;
  }
  
  lookupC(tok) {
    for (const frame of [...this.stack].reverse()) {
      if (frame.c.has(tok)) {
        return true;
      }
    }
    return false;
  }
  
  addF(varz, kind, label) {
    if (!this.lookupV(varz)) {
      throw new Error(`var "${varz}" in $f not defined.`);
    }
    if (!this.lookupC(kind)) {
      throw new Error(`const in $f not defined: ${kind}.`);
    }
    
    const frame = this.top();
    
    if (Object.keys(frame.f_labels).includes(varz)) {
      throw new Error(`var ${varz} in $f already defined in scope`);
    }

    // console.log(label);
    
    frame.f.push([varz, kind]);
    frame.f_labels[varz] = label;
  }
    
  addE(rule, kind, label) {
    const frame = this.top();
    frame.e.push([rule, kind, label]);
    const tag = [rule, kind].flat().join("");
    frame.e_labels[tag] = label;
  }

  addD([d, vars]) {
    const frame = this.top();
    if (vars.length < 2) {
      throw new Error(`Invalid disjoint statement: need at least two variables.`);
    }

    const declared = (variable) => {
      for (const frame of [...this.stack].reverse()) {
        if (frame.v.has(variable)) {
          return true;
        }
      }
      return false;
    }
    
    for (const variable of vars) {
      if (!declared(variable)) {
        throw new Error(`Disjoint statement of undeclared variable ${variable}.`);
      }
    }

    const contains = (pair) => {
      for (const prior of frame.d) {
        if (prior[0] == pair[0] && prior[1] == pair[1]) {
          return true;
        }
      }
      return false;
    }
    
    for (let i = 0; i < vars.length; i++) {
      for (let j = i + 1; j < vars.length; j++) {
        const a = vars[i];
        const b = vars[j];
        const pair = a < b ? [a, b] : [b, a];
        if (!contains(pair)) {
          frame.d.add(pair);
        }
      }
    }
  }

  lookupF(varz) {
    for (const frame of [...this.stack].reverse()) {
      if (frame.f_labels[varz]) {
        return frame.f_labels[varz];
      }
    }
    throw new Error(`Undeclared type of "${varz}".`);
  }

  lookupE(rule, kind) {
    const tag = [rule, kind].flat().join("");
    for (const frame of [...this.stack].reverse()) {
      if (frame.e_labels[tag]) {
        return frame.e_labels[tag];
      }
    }        
    throw new Error(`Undeclared logical requirement "${tag}".`);
  }

  lookupD(a, b) {
    
    for (const frame of [...this.stack].reverse()) {
      // console.log();
      const pair = a < b ? [a, b] : [b, a];
      //console.log(frame.d);
      // console.log(pair);
      //console.log(frame.d.has(pair));
      
      for (let [x, y] of frame.d) {
        // console.log(x);
        if (x == pair[0] && y == pair[1]) {
          // console.log("hi");
          return true;
        }
      }
      // console.log(varz);
      //if (frame.d.has(varz)) {
      //  return frame.d.get(varz);
      //}
    }
    throw new Error(`Undeclared disjoint variable "${a}" and "${b}".`);
  }

  assert(type, rule) {
    const frame = this.top();
    const e = this.stack
          .map((frame) => frame.e)
          .flat();
    
    const mandatory = new Set();

    for (const [hyp] of [...e, [rule, type]]) {
      for (const tok of hyp) {
        // console.log(hyp);
        if (this.lookupV(tok) && this.lookupF(tok)) {
          mandatory.add(tok);
        } else if (!this.lookupC(tok)) {
          throw new Error(`Undeclared token: "${tok}" is neither a constant nor a variable.`);
        }
      }
    }

    const dvs = [];
    for (const {d} of [...this.stack].reverse()) {
      for (const pair of d) {
        const [x, y] = pair;
        // If any of the disjoined variables declarations
        // refer to the mandatory variables, add that
        // condition to the assertion.
        if (mandatory.has(x) && mandatory.has(y)) {
          dvs.push(pair);
        }
      }
    }
      
    const f = [];

    for (const frame of [...this.stack].reverse()) {
      for (const [v, k, label] of [...frame.f].reverse()) {
        if (mandatory.has(v)) {
          f.unshift([k, v, frame.f_labels[v]]);
          mandatory.delete(v);
        }
      }
    }
    
    return [dvs, f, e, [type, rule]];
  }
}

class MM {
  constructor(debug = false) {
    this.frames = new Stack();
    this.labels = {};
    this.debug = debug;
  }

  push() {
    this.frames.push();
  }

  pop() {
    return this.frames.pop();
  }
  
  feed(statements) {
    for (const stmt of statements) {
      const [first, second] = stmt;
      if (first == "$c") {
        const [, vars] = stmt;
        for (const varz of vars) {
          this.frames.addC(varz);
        }
        this.labels["$c"] ||= [];
        this.labels["$c"].push(stmt);
      } else if (first == "$v") {
        const [, vars] = stmt;
        for (const varz of vars) {
          this.frames.addV(varz);
        }
        this.labels["$v"] ||= [];
        this.labels["$v"].push(stmt);
      } else if (first == "${") {
        const [p, inner, q] = stmt;
        this.read(inner);
      } else if (second == "$f") {
        const [label, f, type, variable] = stmt;
        this.frames.addF(variable, type, label);
        this.labels[label] = [f, [type, variable]];
      } else if (first == "$d") {
        this.frames.addD(stmt);
      } else if (second == "$a") {
        const [label, a, type, rule] = stmt;
        const axiom = this.frames.assert(type, rule);
        this.labels[label] = [a, axiom];
      } else if (second == "$e") {
        const [label, e, type, rule] = stmt;
        this.frames.addE(rule, type, label);
        this.labels[label] = [e, [type, rule]];
      } else if (second == "$p") {
        const [label, p, type, theorem, d, proof] = stmt;

        let result = {};
        if (proof[0] != "(") {
          result = (generate = true) => {
            return this.verify(label, type, theorem, proof, generate);
          }
        } else {
          const [d, f, e] = this.frames.assert(type, theorem);
          const labels = [];
          const args = f
                .map(([k, v]) => v)
                .map((v) => this.frames.lookupF(v));
          const hyps = e
                .map(([rule, type]) => this.frames.lookupE(rule, type));
          labels.push(...args);
          labels.push(...hyps);
          result = (generate = true) => {
            let p = this.decompress(proof, labels);
            return this.verify(label, type, theorem, p, generate);
          }
        }
        
        if (!this.verify) {
          result(false);
        }
        // console.log(stmt);
        this.labels[label] = [p, this.frames.assert(type, theorem), result, proof, theorem];
      } else {
        throw new Error(`Unknown statement type: ${stmt}.`);
      }
    }
  }
  
  read(statements) {
    this.frames.push();
    this.feed(statements);
    return this.frames.pop();
  }

  // Algorithms from:
  // https://us.metamath.org/downloads/metamath.pdf
  // https://mm.ivank.net/js/MM.js
  // https://github.com/david-a-wheeler/mmverify.py/blob/master/mmverify.py

  decompress(proof, labels) {
    const m = labels.length;

    const [l, local, r, compressed] = proof;
    
    const n = local.length;

    let integers = [];
    let current = 0;

    // removes whitespaces from the compressed proof
    for (let ch of compressed.replace(/\s/g, "")) {
      if (ch >= 'A' && ch <= 'T') {
        // Shift the current integer left by 20 bits.
        // Add the next 20 bits as the least significant bits.
        const result = current * 20 + ch.charCodeAt(0) - 'A'.charCodeAt(0) + 1;
        integers.push(result);
        // Reset the current integer.
        current = 0;
      } else if (ch >= 'U' && ch <= 'Y') {
        // Shift the current integer left by 5 bits.
        current = current * 5;
        // Add the next 5 bits as the last significant bits.
        current += ch.charCodeAt(0) - 'U'.charCodeAt(0) + 1;
      } else if (ch == 'Z') {
        integers.push(-1);
      } else {
        throw new Error(`Unexpected character "${ch}" in compressed proof`);
      }
    }

    // console.log(integers);
    
    const steps = integers.map((integer) => {
      if (integer == -1) {
        return -1;
        return integer;
      } else if (integer > 0 && integer <= m) {
        return labels[integer - 1];
      } else if (integer > m && integer <= (m + n)) {
        const i = integer - m;
        return local[i - 1];
      } else {
        // A marker.
        return integer - (m + n + 1);
      }
    });

    const statements = this.labels;
    
    function tree(i) {
      if (!statements[steps[i]]) {
        throw new Error(`Can't find entry ${steps[i]}.`);
      }
      const [type, [dvs, f = [], e = []]] = statements[steps[i]];
      let result = 0;
      if (type == "$f" || type == "$e") {
        return 1;
      } else if (type == "$a" || type == "$p") {
        for (let j = 0; j < (f.length + e.length); j++) {
          const offset = tree(i - 1 - result);
          result += offset;
        }
      }
      return result + 1;
    }

    const markers = [];

    let i = 0;
    while (i < steps.length) {
      const number = steps[i];
      if (typeof steps[i] == "string") {
        i++;
      } else if (number == -1) {
        // push the subtree to the markers
        const size = tree(i - 1);
        const subtree = steps.slice(i - size, i);
        markers.push(subtree);
        // delete the marker
        steps.splice(i, 1);
      } else if (!markers[number]) {
        throw new Error(`Marker #${number} not found while unrolling ${proof.join('')}.`);
      } else {
        // replace the number with the marked subtree
        // https://stackoverflow.com/questions/44959025/rangeerror-maximum-call-stack-size-exceeded-caused-by-array-splice-apply
        if (markers[number].length > 65536) {
          // console.log(markers[number]);
          // console.log(compressed);
          throw new Error("proof too long");
        }
        steps.splice(i, 1, ...markers[number]);
      }
    }

    return steps;
  }

  verify(label, type, theorem, proof, generate) {
    const stack = [];

    const steps = [];

    let index = 0;
    for (const step of proof) {
      if (!this.labels[step]) {
        throw new Error(`Unknown theorem "${step}" in the proof for "${label}".`);
      }
      const [op, data] = this.labels[step];
      if (op == "$e" || op == "$f") {
        const [type, varz] = data;
        stack.push([index, type, [varz]]);
        const t = stack[stack.length - 1];
        steps.push([step, [t[1], t[2]], []]);
      } else if (op == "$a" || op == "$p") {
        const [dvs, mandatory, hyp, result] = data;
        const subs = {};
        const npop = mandatory.length + hyp.length;
        const base = stack.length - npop;
        // console.log(`Stack: base=${base}, npop=${npop}, length=${stack.length}`);
        const args = [];
        let sp = base;
        if (sp < 0) {
          throw new Error(`Empty stack ${sp}.`);
        }
        
        for (const [k, v] of mandatory) {
          const top = stack[sp];
          if (top[1] != k) {
            console.log(`Stack at ${sp} because ${mandatory.length} args + ${hyp.length} hypothesis:`);
            for (let [index, type, string] of stack.reverse()) {
              console.log(`  ${type} ${string.join("")}`);
            }
            console.log(mandatory);
            throw new Error(`Step ${step} of ${label}: argument type of ${v} doesn't match with the top of the stack. Expected ${k} but got ${top[1]}.`);
          }
          subs[v] = top[2];
          args.push(top[0]);
          sp++;
        }
        
        for (const [h, type] of hyp) {
          const top = stack[sp];
          if (top[1] != type) {
            throw new Error(`Step ${step}: argument type doesn't match with the topf of the stack. Expected ${type} but got ${top[0]}.`);
          }
          
          const sub = h
                .map((tok) => subs[tok] ? subs[tok] : tok);
          if (top[2].flat().join("") != sub.flat().join("")) {
            // argument value for substitution ${JSON.stringify(subs)} of the hypothesis ${h.join(" ")} doesn't match with the top of the stack. 
            throw new Error(`Step ${step}: Expected ${sub.flat().join("")} but got ${top[2].join("")}.`);
          }
          args.push(top[0]);
          sp++;
        }

        // Page 133: Verifying Disjoint Variable Restrictions
        // https://us.metamath.org/downloads/metamath.pdf
        // Each substitution made in a proof must be checked to verify that any disjoint
        // variable restrictions are satisfied, as follows.
        // If two variables replaced by a substitution exist in a mandatory $d
        // statement of the assertion referenced, the two expressions resulting from the
        // substitution must satisfy the following conditions.
        if (!generate) {
          // If we are in debug mode, skip this.
          for (const [x, y] of dvs) {
            const a = subs[x].filter((v) => this.frames.lookupV(v));
            const b = subs[y].filter((v) => this.frames.lookupV(v));
            for (let el1 of a) {
              for (let el2 of b) {
                // First, the two expressions must have no variables in common.
                if (el1 == el2) {
                  throw new Error(`${x} (${a}) and ${y} (${b}) are disjoined variables, and they share ${el}. `);
                }
                
                // Second, each possible pair of variables, one from each expression, must exist in
                // an active $d statement of the $p statement containing the proof.
                if (!this.frames.lookupD(el1, el2)) {
                  throw new Error(`${el1} of ${x} (${a}) and ${el2} of ${y} (${b}) aren't declared as disjoint.`);
                }
              }
            }
          }
        }
        
        stack.splice(base, npop);
        
        const el = result[1]
              .map((tok) => subs[tok] ? subs[tok] : tok);

        stack.push([index, result[0], el.flat()]);
        const t = stack[stack.length - 1];
        steps.push([step, [t[1], t[2]], args]);
      }

      index++;
    }

    if (stack.length != 1) {
      throw new Error(`Stack has more than one entry left`);
    }
    
    const [, kind, last] = stack.pop();

    if (type != kind) {
      throw new Error(`Assertion proved doesn't match: expected ${type} but got ${kind}`);
    }
    
    if (last.flat().join(" ") != theorem.flat().join(" ")) {
      console.log(last);
      console.log(theorem);
      throw new Error(`Assertion proved doesn't match: expected ${theorem.join("")} but got ${last.join("")}`);
    }

    return steps;
  }

  theorem(name) {
    const [, , proof] = this.labels[name];
    return [name, proof];   
  }
  
  theorems() {
    return Object.entries(this.labels)
          .filter(([key, [type]]) => type == "$p")
          .map(([key, [type, header, proof]]) => [key, proof]);
  }
  
  verifyAll() {
    // return 1;
    // console.log(this);
    const theorems = this.theorems();
    for (let [name, proof] of theorems) {
      //try {
      proof();
      //} catch (e) {
        // TODO(goto): deal with array splicing limits.
      //  if (e.message == "proof too long") {
      //    console.log(`Skipping ${label} because the proof is too long.`);
      //  } else {
      //    throw e;
      // }
      //}
    }
    return theorems.length;
  }
}


module.exports = {
  Frame: Frame,
  Stack: Stack,
  MM: MM
};
