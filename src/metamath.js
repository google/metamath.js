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

  hasF(label) {
    for (const {f_labels} of [...this.stack].reverse()) {
      for (const [varz, name] of Object.entries(f_labels)) {
        if (label == name) {
          return varz;
        }
      }
    }
    return false;
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
      const pair = a < b ? [a, b] : [b, a];
      
      for (let [x, y] of frame.d) {
        if (x == pair[0] && y == pair[1]) {
          return true;
        }
      }
    }
    throw new Error(`Undeclared disjoint variable "${a}" and "${b}".`);
  }

  assert(type, rule, proof) {
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
    const dummies = [];
    const dummy = {};
    for (const {d} of [...this.stack].reverse()) {
      for (const pair of d) {
        const [x, y] = pair;
        // If any of the disjoined variables declarations
        // refer to the mandatory variables, add that
        // condition to the assertion.
        if (mandatory.has(x) && mandatory.has(y)) {
          dvs.push(pair);
        } else {
          dummies.push(pair);
          // Capture dummy variables (variables that are
          // used internally in proofs but don't who up
          // in the header of the theorem) and their
          // disjointness requirements.

          // TODO: we should probably store the types
          // here too, rather than just the label
          // references, since the labels can be overriden
          // in different scopes.
          if (!mandatory.has(x)) {
            dummy[x] = this.lookupF(x);
          }
          if (!mandatory.has(y)) {
            dummy[y] = this.lookupF(y);
          }
        }
      }
    }

    if (proof) {
      // NOTE: this is extremely slow, because it has to
      // compute wether a label is a $f statement for each
      // step of the proof, and $f statements can be made
      // anywhere in the stack.
      for (const step of proof[0] == "(" ? proof[1] : proof) {
        const varz = this.hasF(step);
        if (varz && !mandatory.has(varz)) {
          dummy[varz] = this.lookupF(varz);
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
    
    return [dvs, f, e, [type, rule], dummies, dummy];
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
        const assertion = this.frames.assert(type, theorem, proof);
        if (proof[0] != "(") {
          result = (generate = true) => {
            return this.verify(label, type, theorem, proof, generate);
          }
        } else {
          const [d, f, e] = assertion;
          const labels = [];
          const args = f
                .map(([k, v]) => v)
                .map((v) => this.frames.lookupF(v));
          const hyps = e
                .map(([rule, type]) => this.frames.lookupE(rule, type));
          labels.push(...args);
          labels.push(...hyps);
          result = (generate = true, markers = true) => {
            const [, external, , compressed] = proof;
            let p = markers ?
                new Decompressor().decompress(labels, external, compressed) :
                new Decompressor().explode(labels, external, compressed, this.labels);
            return this.verify(label, type, theorem, p, generate);
          }

          // const labels = this.labels;
          const that = this;
          proof.decompress = () => {
            const [, external, , compressed] = proof;
            return new Decompressor().decompress(labels, external, compressed);
          }
          proof.explode = () => {
            const [, external, , compressed] = proof;
            return new Decompressor().explode(labels, external, compressed, that.labels);
          }
        }
        
        if (!this.verify) {
          result(false);
        }
        // console.log(stmt);
        // throw new Error("hi");
        this.labels[label] = [p, assertion, result, proof, theorem];
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

  print() {

  }
  
  verify(label, type, theorem, proof, generate) {
    const stack = [];
    const steps = [];
    const markers = [];

    // throw new Error("hi");
    
    let index = 0;
    for (const step of proof) {
      if (step == -1) {
        // Take the top of the stack, which is the result of
        // a prior computation / verification, and saves that
        // result so that it can be reused later, without
        // incurring into the recomputation.
        const top = stack[stack.length - 1];
        markers.push([top, index - 1]);
        steps.push([step, top.slice(1), index - 1]);
        continue;
      } else if (typeof step == "number") {
        // Takes a prior computation, which was already
        // previously verified (since it was at the top of
        // the stack at some point), and reuses its result
        // in another computation by pushing it into the stack.
        // stack.push(markers[step]);
        if (!markers[step]) {
          throw new Error(`Can't find marker for ${step}: ${Object.keys(markers)}.`);
        }
        const [[, type, string], i] = markers[step];
        // Reuse the computation from a previous step, but generate
        // a new step entry.
        stack.push([index, type, string]);
        // throw new Error(step);
        steps.push([step, [type, string], i]);
        // continue;
      } else {
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
            throw new Error(`Step ${step}: empty stack ${sp} (length = ${stack.length} and popping = ${npop}).`);
          }
        
          for (const [k, v] of mandatory) {
            const top = stack[sp];
            if (top[1] != k) {
              console.log(`Stack at ${sp} because ${mandatory.length} args + ${hyp.length} hypothesis:`);
              for (let [index, type, string] of stack.reverse()) {
                console.log(`  ${type} ${string.flat().join(" ")}`);
              }
              // console.log(mandatory);
              throw new Error(`Step "${step}" of "${label}": argument type of "${v}" doesn't match with the top of the stack. Expected "${k}" but got "${top[1]}" (${top[2].flat().join(" ")}).`);
            }
            subs[v] = top[2];
            args.push(top[0]);
            sp++;
          }
        
          for (const [h, type] of hyp) {
            const top = stack[sp];
            if (top[1] != type) {
              throw new Error(`Step ${step}: argument type doesn't match with the top of the stack. Expected ${type} but got ${top[1]}.`);
            }
          
            const sub = h
                  .map((tok) => subs[tok] ? subs[tok] : tok);
            if (top[2].flat().join("") != sub.flat().join("")) {
              const e = [];
              e.push(`Substitution ${JSON.stringify(subs)} of the hypothesis ${h.join(" ")} doesn't match with the top of the stack`);
              e.push(`Step ${step}: Expected ${sub.flat().join(" ")} but got ${top[2].flat().join(" ")}.`);
              throw new Error(e.join("\n"));
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
                    throw new Error(`${x} (=${a}) and ${y} (=${b}) are disjoined variables and can't carry the same value. `);
                  }
                  // console.log(label);
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
      }

      index++;
    }

    if (stack.length != 1) {
      const message = [];
      message.push(`Stack has more than one entry left:\n`);
      for (let [index, type, string] of stack.reverse()) {
        message.push(`  ${type} ${string.flat().join(" ")}`);
      }
      throw new Error(message.join("\n"));
    }
    
    const [, kind, last] = stack.pop();

    if (type != kind) {
      throw new Error(`Assertion proved doesn't match: expected ${type} but got ${kind}`);
    }
    
    if (last.flat().join(" ") != theorem.flat().join(" ")) {
      throw new Error(`Result of proof doesn't match assertion: expected "${theorem.join(" ")}" but got "${last.join(" ")}".`);
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

class Decompressor {
  decode(compressed) {
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

    return integers;
  }


  // Algorithms from:
  // https://us.metamath.org/downloads/metamath.pdf
  // https://mm.ivank.net/js/MM.js
  // https://github.com/david-a-wheeler/mmverify.py/blob/master/mmverify.py

  steps(labels, local, integers) {
    const m = labels.length;
    const n = local.length;

    return integers.map((integer) => {
      if (integer == -1) {
        return -1;
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
  }

  tree(steps, i, other) {
    // const statements = this.labels;
    const statements = other;

    if (!statements[steps[i]]) {
      throw new Error(`Can't find entry ${steps[i]}.`);
    }
    const [type, [dvs, f = [], e = []]] = statements[steps[i]];
    let result = 0;
    if (type == "$f" || type == "$e") {
      return 1;
    } else if (type == "$a" || type == "$p") {
      for (let j = 0; j < (f.length + e.length); j++) {
        const offset = this.tree(steps, i - 1 - result, other);
        result += offset;
      }
    }
    return result + 1;
  }

  expand(steps, other) {
    const markers = [];

    let i = 0;
    while (i < steps.length) {
      const number = steps[i];
      if (typeof steps[i] == "string") {
        i++;
      } else if (number == -1) {
        // push the subtree to the markers
        const size = this.tree(steps, i - 1, other);
        const subtree = steps.slice(i - size, i);
        markers.push(subtree);
        // delete the marker
        steps.splice(i, 1);
      } else if (!markers[number]) {
        // console.log(other);
        throw new Error(`Marker #${number} not found while unrolling proof.`);
      } else {
        // replace the number with the marked subtree
        // https://stackoverflow.com/questions/44959025/rangeerror-maximum-call-stack-size-exceeded-caused-by-array-splice-apply
        if (markers[number].length > 65536) {
          throw new Error("proof too long");
        }
        steps.splice(i, 1, ...markers[number]);
      }
    }

    return steps;
  }

  decompress(local, external, compressed) {
    // We can either choose to decompress the proof using
    // markers, which substantially speed up the processing
    // by reusing prior computation.
    let integers = this.decode(compressed);
    return this.steps(local, external, integers);
  }
  
  explode(local, external, compressed, other) {
    // Or we can expand the proof fully, which recomputes
    // all subproofs.
    const steps = this.decompress(local, external, compressed);
    return this.expand(steps, other);
  }


}

class Compressor {
  constructor(local, steps) {
    this.steps = steps;
    this.local = local;
  }
  
  external() {
    // throw new Error("hi");
    return this.steps
      .filter((step) => typeof step != "number")
      .filter((label) => !this.local.includes(label))
      .filter((label, i, self) => self.indexOf(label) == i);
  }
  
  integers() {
    let labels = this.local;
    let refs = this.external();
    return this.steps.map((step) => {
      if (step == -1) {
        // A marker
        return step;
      } else if (labels.includes(step)) {
        // A hypothesis reference
        return 1 + labels.indexOf(step);
      } else if (refs.includes(step)) {
        // A local array reference
        return 1 + labels.length + refs.indexOf(step);
      } else if (typeof step == "number") {
        // A reference to a marker
        return 1 + labels.length + refs.length + step;
      } else {
        throw new Error(`Invalid ${step}`);
      }
    });
  }

  compress() {
    return this.integers()
      .map((number) => number == -1 ? "Z" : Compressor.encode(number))
      .join("");
  }
    
  static encode(number) {
    const digits = [];
      
    let n = number - 1;

    let msb = Math.floor(n / 20);
      
    while (msb > 0) {
      const ch = String.fromCharCode('U'.charCodeAt(0) + ((msb - 1) % 5));
      digits.push(ch);
      msb = Math.floor((msb - 1) / 5);
    }
      
    const remainder = n % 20;
    digits.push(String.fromCharCode('A'.charCodeAt(0) + remainder));
    return digits.join("");
  }
}

module.exports = {
  Frame: Frame,
  Stack: Stack,
  MM: MM,
  Compressor: Compressor,
  Decompressor: Decompressor,
};
