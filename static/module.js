(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define([],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}g.module = f()}})(function(){var define,module,exports;return (function(){function r(e,n,t){function o(i,f){if(!n[i]){if(!e[i]){var c="function"==typeof require&&require;if(!f&&c)return c(i,!0);if(u)return u(i,!0);var a=new Error("Cannot find module '"+i+"'");throw a.code="MODULE_NOT_FOUND",a}var p=n[i]={exports:{}};e[i][0].call(p.exports,function(r){var n=e[i][1][r];return o(n||r)},p,p.exports,r,e,n,t)}return n[i].exports}for(var u="function"==typeof require&&require,i=0;i<t.length;i++)o(t[i]);return o}return r})()({1:[function(require,module,exports){
(function(root, factory) {
  if (typeof define === 'function' && define.amd) {
    define([], factory) /* global define */
  } else if (typeof module === 'object' && module.exports) {
    module.exports = factory()
  } else {
    root.moo = factory()
  }
}(this, function() {
  'use strict';

  var hasOwnProperty = Object.prototype.hasOwnProperty
  var toString = Object.prototype.toString
  var hasSticky = typeof new RegExp().sticky === 'boolean'

  /***************************************************************************/

  function isRegExp(o) { return o && toString.call(o) === '[object RegExp]' }
  function isObject(o) { return o && typeof o === 'object' && !isRegExp(o) && !Array.isArray(o) }

  function reEscape(s) {
    return s.replace(/[-\/\\^$*+?.()|[\]{}]/g, '\\$&')
  }
  function reGroups(s) {
    var re = new RegExp('|' + s)
    return re.exec('').length - 1
  }
  function reCapture(s) {
    return '(' + s + ')'
  }
  function reUnion(regexps) {
    if (!regexps.length) return '(?!)'
    var source =  regexps.map(function(s) {
      return "(?:" + s + ")"
    }).join('|')
    return "(?:" + source + ")"
  }

  function regexpOrLiteral(obj) {
    if (typeof obj === 'string') {
      return '(?:' + reEscape(obj) + ')'

    } else if (isRegExp(obj)) {
      // TODO: consider /u support
      if (obj.ignoreCase) throw new Error('RegExp /i flag not allowed')
      if (obj.global) throw new Error('RegExp /g flag is implied')
      if (obj.sticky) throw new Error('RegExp /y flag is implied')
      if (obj.multiline) throw new Error('RegExp /m flag is implied')
      return obj.source

    } else {
      throw new Error('Not a pattern: ' + obj)
    }
  }

  function objectToRules(object) {
    var keys = Object.getOwnPropertyNames(object)
    var result = []
    for (var i = 0; i < keys.length; i++) {
      var key = keys[i]
      var thing = object[key]
      var rules = [].concat(thing)
      if (key === 'include') {
        for (var j = 0; j < rules.length; j++) {
          result.push({include: rules[j]})
        }
        continue
      }
      var match = []
      rules.forEach(function(rule) {
        if (isObject(rule)) {
          if (match.length) result.push(ruleOptions(key, match))
          result.push(ruleOptions(key, rule))
          match = []
        } else {
          match.push(rule)
        }
      })
      if (match.length) result.push(ruleOptions(key, match))
    }
    return result
  }

  function arrayToRules(array) {
    var result = []
    for (var i = 0; i < array.length; i++) {
      var obj = array[i]
      if (obj.include) {
        var include = [].concat(obj.include)
        for (var j = 0; j < include.length; j++) {
          result.push({include: include[j]})
        }
        continue
      }
      if (!obj.type) {
        throw new Error('Rule has no type: ' + JSON.stringify(obj))
      }
      result.push(ruleOptions(obj.type, obj))
    }
    return result
  }

  function ruleOptions(type, obj) {
    if (!isObject(obj)) {
      obj = { match: obj }
    }
    if (obj.include) {
      throw new Error('Matching rules cannot also include states')
    }

    // nb. error and fallback imply lineBreaks
    var options = {
      defaultType: type,
      lineBreaks: !!obj.error || !!obj.fallback,
      pop: false,
      next: null,
      push: null,
      error: false,
      fallback: false,
      value: null,
      type: null,
      shouldThrow: false,
    }

    // Avoid Object.assign(), so we support IE9+
    for (var key in obj) {
      if (hasOwnProperty.call(obj, key)) {
        options[key] = obj[key]
      }
    }

    // type transform cannot be a string
    if (typeof options.type === 'string' && type !== options.type) {
      throw new Error("Type transform cannot be a string (type '" + options.type + "' for token '" + type + "')")
    }

    // convert to array
    var match = options.match
    options.match = Array.isArray(match) ? match : match ? [match] : []
    options.match.sort(function(a, b) {
      return isRegExp(a) && isRegExp(b) ? 0
           : isRegExp(b) ? -1 : isRegExp(a) ? +1 : b.length - a.length
    })
    return options
  }

  function toRules(spec) {
    return Array.isArray(spec) ? arrayToRules(spec) : objectToRules(spec)
  }

  var defaultErrorRule = ruleOptions('error', {lineBreaks: true, shouldThrow: true})
  function compileRules(rules, hasStates) {
    var errorRule = null
    var fast = Object.create(null)
    var fastAllowed = true
    var unicodeFlag = null
    var groups = []
    var parts = []

    // If there is a fallback rule, then disable fast matching
    for (var i = 0; i < rules.length; i++) {
      if (rules[i].fallback) {
        fastAllowed = false
      }
    }

    for (var i = 0; i < rules.length; i++) {
      var options = rules[i]

      if (options.include) {
        // all valid inclusions are removed by states() preprocessor
        throw new Error('Inheritance is not allowed in stateless lexers')
      }

      if (options.error || options.fallback) {
        // errorRule can only be set once
        if (errorRule) {
          if (!options.fallback === !errorRule.fallback) {
            throw new Error("Multiple " + (options.fallback ? "fallback" : "error") + " rules not allowed (for token '" + options.defaultType + "')")
          } else {
            throw new Error("fallback and error are mutually exclusive (for token '" + options.defaultType + "')")
          }
        }
        errorRule = options
      }

      var match = options.match.slice()
      if (fastAllowed) {
        while (match.length && typeof match[0] === 'string' && match[0].length === 1) {
          var word = match.shift()
          fast[word.charCodeAt(0)] = options
        }
      }

      // Warn about inappropriate state-switching options
      if (options.pop || options.push || options.next) {
        if (!hasStates) {
          throw new Error("State-switching options are not allowed in stateless lexers (for token '" + options.defaultType + "')")
        }
        if (options.fallback) {
          throw new Error("State-switching options are not allowed on fallback tokens (for token '" + options.defaultType + "')")
        }
      }

      // Only rules with a .match are included in the RegExp
      if (match.length === 0) {
        continue
      }
      fastAllowed = false

      groups.push(options)

      // Check unicode flag is used everywhere or nowhere
      for (var j = 0; j < match.length; j++) {
        var obj = match[j]
        if (!isRegExp(obj)) {
          continue
        }

        if (unicodeFlag === null) {
          unicodeFlag = obj.unicode
        } else if (unicodeFlag !== obj.unicode && options.fallback === false) {
          throw new Error('If one rule is /u then all must be')
        }
      }

      // convert to RegExp
      var pat = reUnion(match.map(regexpOrLiteral))

      // validate
      var regexp = new RegExp(pat)
      if (regexp.test("")) {
        throw new Error("RegExp matches empty string: " + regexp)
      }
      var groupCount = reGroups(pat)
      if (groupCount > 0) {
        throw new Error("RegExp has capture groups: " + regexp + "\nUse (?: … ) instead")
      }

      // try and detect rules matching newlines
      if (!options.lineBreaks && regexp.test('\n')) {
        throw new Error('Rule should declare lineBreaks: ' + regexp)
      }

      // store regex
      parts.push(reCapture(pat))
    }


    // If there's no fallback rule, use the sticky flag so we only look for
    // matches at the current index.
    //
    // If we don't support the sticky flag, then fake it using an irrefutable
    // match (i.e. an empty pattern).
    var fallbackRule = errorRule && errorRule.fallback
    var flags = hasSticky && !fallbackRule ? 'ym' : 'gm'
    var suffix = hasSticky || fallbackRule ? '' : '|'

    if (unicodeFlag === true) flags += "u"
    var combined = new RegExp(reUnion(parts) + suffix, flags)
    return {regexp: combined, groups: groups, fast: fast, error: errorRule || defaultErrorRule}
  }

  function compile(rules) {
    var result = compileRules(toRules(rules))
    return new Lexer({start: result}, 'start')
  }

  function checkStateGroup(g, name, map) {
    var state = g && (g.push || g.next)
    if (state && !map[state]) {
      throw new Error("Missing state '" + state + "' (in token '" + g.defaultType + "' of state '" + name + "')")
    }
    if (g && g.pop && +g.pop !== 1) {
      throw new Error("pop must be 1 (in token '" + g.defaultType + "' of state '" + name + "')")
    }
  }
  function compileStates(states, start) {
    var all = states.$all ? toRules(states.$all) : []
    delete states.$all

    var keys = Object.getOwnPropertyNames(states)
    if (!start) start = keys[0]

    var ruleMap = Object.create(null)
    for (var i = 0; i < keys.length; i++) {
      var key = keys[i]
      ruleMap[key] = toRules(states[key]).concat(all)
    }
    for (var i = 0; i < keys.length; i++) {
      var key = keys[i]
      var rules = ruleMap[key]
      var included = Object.create(null)
      for (var j = 0; j < rules.length; j++) {
        var rule = rules[j]
        if (!rule.include) continue
        var splice = [j, 1]
        if (rule.include !== key && !included[rule.include]) {
          included[rule.include] = true
          var newRules = ruleMap[rule.include]
          if (!newRules) {
            throw new Error("Cannot include nonexistent state '" + rule.include + "' (in state '" + key + "')")
          }
          for (var k = 0; k < newRules.length; k++) {
            var newRule = newRules[k]
            if (rules.indexOf(newRule) !== -1) continue
            splice.push(newRule)
          }
        }
        rules.splice.apply(rules, splice)
        j--
      }
    }

    var map = Object.create(null)
    for (var i = 0; i < keys.length; i++) {
      var key = keys[i]
      map[key] = compileRules(ruleMap[key], true)
    }

    for (var i = 0; i < keys.length; i++) {
      var name = keys[i]
      var state = map[name]
      var groups = state.groups
      for (var j = 0; j < groups.length; j++) {
        checkStateGroup(groups[j], name, map)
      }
      var fastKeys = Object.getOwnPropertyNames(state.fast)
      for (var j = 0; j < fastKeys.length; j++) {
        checkStateGroup(state.fast[fastKeys[j]], name, map)
      }
    }

    return new Lexer(map, start)
  }

  function keywordTransform(map) {
    var reverseMap = Object.create(null)
    var byLength = Object.create(null)
    var types = Object.getOwnPropertyNames(map)
    for (var i = 0; i < types.length; i++) {
      var tokenType = types[i]
      var item = map[tokenType]
      var keywordList = Array.isArray(item) ? item : [item]
      keywordList.forEach(function(keyword) {
        (byLength[keyword.length] = byLength[keyword.length] || []).push(keyword)
        if (typeof keyword !== 'string') {
          throw new Error("keyword must be string (in keyword '" + tokenType + "')")
        }
        reverseMap[keyword] = tokenType
      })
    }

    // fast string lookup
    // https://jsperf.com/string-lookups
    function str(x) { return JSON.stringify(x) }
    var source = ''
    source += 'switch (value.length) {\n'
    for (var length in byLength) {
      var keywords = byLength[length]
      source += 'case ' + length + ':\n'
      source += 'switch (value) {\n'
      keywords.forEach(function(keyword) {
        var tokenType = reverseMap[keyword]
        source += 'case ' + str(keyword) + ': return ' + str(tokenType) + '\n'
      })
      source += '}\n'
    }
    source += '}\n'
    return Function('value', source) // type
  }

  /***************************************************************************/

  var Lexer = function(states, state) {
    this.startState = state
    this.states = states
    this.buffer = ''
    this.stack = []
    this.reset()
  }

  Lexer.prototype.reset = function(data, info) {
    this.buffer = data || ''
    this.index = 0
    this.line = info ? info.line : 1
    this.col = info ? info.col : 1
    this.queuedToken = info ? info.queuedToken : null
    this.queuedThrow = info ? info.queuedThrow : null
    this.setState(info ? info.state : this.startState)
    this.stack = info && info.stack ? info.stack.slice() : []
    return this
  }

  Lexer.prototype.save = function() {
    return {
      line: this.line,
      col: this.col,
      state: this.state,
      stack: this.stack.slice(),
      queuedToken: this.queuedToken,
      queuedThrow: this.queuedThrow,
    }
  }

  Lexer.prototype.setState = function(state) {
    if (!state || this.state === state) return
    this.state = state
    var info = this.states[state]
    this.groups = info.groups
    this.error = info.error
    this.re = info.regexp
    this.fast = info.fast
  }

  Lexer.prototype.popState = function() {
    this.setState(this.stack.pop())
  }

  Lexer.prototype.pushState = function(state) {
    this.stack.push(this.state)
    this.setState(state)
  }

  var eat = hasSticky ? function(re, buffer) { // assume re is /y
    return re.exec(buffer)
  } : function(re, buffer) { // assume re is /g
    var match = re.exec(buffer)
    // will always match, since we used the |(?:) trick
    if (match[0].length === 0) {
      return null
    }
    return match
  }

  Lexer.prototype._getGroup = function(match) {
    var groupCount = this.groups.length
    for (var i = 0; i < groupCount; i++) {
      if (match[i + 1] !== undefined) {
        return this.groups[i]
      }
    }
    throw new Error('Cannot find token type for matched text')
  }

  function tokenToString() {
    return this.value
  }

  Lexer.prototype.next = function() {
    var index = this.index

    // If a fallback token matched, we don't need to re-run the RegExp
    if (this.queuedGroup) {
      var token = this._token(this.queuedGroup, this.queuedText, index)
      this.queuedGroup = null
      this.queuedText = ""
      return token
    }

    var buffer = this.buffer
    if (index === buffer.length) {
      return // EOF
    }

    // Fast matching for single characters
    var group = this.fast[buffer.charCodeAt(index)]
    if (group) {
      return this._token(group, buffer.charAt(index), index)
    }

    // Execute RegExp
    var re = this.re
    re.lastIndex = index
    var match = eat(re, buffer)

    // Error tokens match the remaining buffer
    var error = this.error
    if (match == null) {
      return this._token(error, buffer.slice(index, buffer.length), index)
    }

    var group = this._getGroup(match)
    var text = match[0]

    if (error.fallback && match.index !== index) {
      this.queuedGroup = group
      this.queuedText = text

      // Fallback tokens contain the unmatched portion of the buffer
      return this._token(error, buffer.slice(index, match.index), index)
    }

    return this._token(group, text, index)
  }

  Lexer.prototype._token = function(group, text, offset) {
    // count line breaks
    var lineBreaks = 0
    if (group.lineBreaks) {
      var matchNL = /\n/g
      var nl = 1
      if (text === '\n') {
        lineBreaks = 1
      } else {
        while (matchNL.exec(text)) { lineBreaks++; nl = matchNL.lastIndex }
      }
    }

    var token = {
      type: (typeof group.type === 'function' && group.type(text)) || group.defaultType,
      value: typeof group.value === 'function' ? group.value(text) : text,
      text: text,
      toString: tokenToString,
      offset: offset,
      lineBreaks: lineBreaks,
      line: this.line,
      col: this.col,
    }
    // nb. adding more props to token object will make V8 sad!

    var size = text.length
    this.index += size
    this.line += lineBreaks
    if (lineBreaks !== 0) {
      this.col = size - nl + 1
    } else {
      this.col += size
    }

    // throw, if no rule with {error: true}
    if (group.shouldThrow) {
      throw new Error(this.formatError(token, "invalid syntax"))
    }

    if (group.pop) this.popState()
    else if (group.push) this.pushState(group.push)
    else if (group.next) this.setState(group.next)

    return token
  }

  if (typeof Symbol !== 'undefined' && Symbol.iterator) {
    var LexerIterator = function(lexer) {
      this.lexer = lexer
    }

    LexerIterator.prototype.next = function() {
      var token = this.lexer.next()
      return {value: token, done: !token}
    }

    LexerIterator.prototype[Symbol.iterator] = function() {
      return this
    }

    Lexer.prototype[Symbol.iterator] = function() {
      return new LexerIterator(this)
    }
  }

  Lexer.prototype.formatError = function(token, message) {
    if (token == null) {
      // An undefined token indicates EOF
      var text = this.buffer.slice(this.index)
      var token = {
        text: text,
        offset: this.index,
        lineBreaks: text.indexOf('\n') === -1 ? 0 : 1,
        line: this.line,
        col: this.col,
      }
    }
    var start = Math.max(0, token.offset - token.col + 1)
    var eol = token.lineBreaks ? token.text.indexOf('\n') : token.text.length
    var firstLine = this.buffer.substring(start, token.offset + eol)
    message += " at line " + token.line + " col " + token.col + ":\n\n"
    message += "  " + firstLine + "\n"
    message += "  " + Array(token.col).join(" ") + "^"
    return message
  }

  Lexer.prototype.clone = function() {
    return new Lexer(this.states, this.state)
  }

  Lexer.prototype.has = function(tokenType) {
    return true
  }


  return {
    compile: compile,
    states: compileStates,
    error: Object.freeze({error: true}),
    fallback: Object.freeze({fallback: true}),
    keywords: keywordTransform,
  }

}));

},{}],2:[function(require,module,exports){
(function (process,__dirname){(function (){
(function(root, factory) {
    if (typeof module === 'object' && module.exports) {
        module.exports = factory(require('./nearley'));
    } else {
        root.Compile = factory(root.nearley);
    }
}(this, function(nearley) {

    function Compile(structure, opts) {
        var unique = uniquer();
        if (!opts.alreadycompiled) {
            opts.alreadycompiled = [];
        }

        var result = {
            rules: [],
            body: [], // @directives list
            customTokens: [], // %tokens
            config: {}, // @config value
            macros: {},
            start: '',
            version: opts.version || 'unknown'
        };

        for (var i = 0; i < structure.length; i++) {
            var productionRule = structure[i];
            if (productionRule.body) {
                // This isn't a rule, it's an @directive.
                if (!opts.nojs) {
                    result.body.push(productionRule.body);
                }
            } else if (productionRule.include) {
                // Include file
                var path;
                if (!productionRule.builtin) {
                    path = require('path').resolve(
                        opts.args[0] ? require('path').dirname(opts.args[0]) : process.cwd(),
                        productionRule.include
                    );
                } else {
                    path = require('path').resolve(
                        __dirname,
                        '../builtin/',
                        productionRule.include
                    );
                }
                if (opts.alreadycompiled.indexOf(path) === -1) {
                    opts.alreadycompiled.push(path);
                    var f = require('fs').readFileSync(path).toString();
                    var parserGrammar = nearley.Grammar.fromCompiled(require('./nearley-language-bootstrapped.js'));
                    var parser = new nearley.Parser(parserGrammar);
                    parser.feed(f);
                    var c = Compile(parser.results[0], {args: [path], __proto__:opts});
                    result.rules = result.rules.concat(c.rules);
                    result.body  = result.body.concat(c.body);
                    result.customTokens = result.customTokens.concat(c.customTokens);
                    Object.keys(c.config).forEach(function(k) {
                        result.config[k] = c.config[k];
                    });
                    Object.keys(c.macros).forEach(function(k) {
                        result.macros[k] = c.macros[k];
                    });
                }
            } else if (productionRule.macro) {
                result.macros[productionRule.macro] = {
                    'args': productionRule.args,
                    'exprs': productionRule.exprs
                };
            } else if (productionRule.config) {
                // This isn't a rule, it's an @config.
                result.config[productionRule.config] = productionRule.value
            } else {
                produceRules(productionRule.name, productionRule.rules, {});
                if (!result.start) {
                    result.start = productionRule.name;
                }
            }
        }

        return result;

        function produceRules(name, rules, env) {
            for (var i = 0; i < rules.length; i++) {
                var rule = buildRule(name, rules[i], env);
                if (opts.nojs) {
                    rule.postprocess = null;
                }
                result.rules.push(rule);
            }
        }

        function buildRule(ruleName, rule, env) {
            var tokens = [];
            for (var i = 0; i < rule.tokens.length; i++) {
                var token = buildToken(ruleName, rule.tokens[i], env);
                if (token !== null) {
                    tokens.push(token);
                }
            }
            return new nearley.Rule(
                ruleName,
                tokens,
                rule.postprocess
            );
        }

        function buildToken(ruleName, token, env) {
            if (typeof token === 'string') {
                if (token === 'null') {
                    return null;
                }
                return token;
            }

            if (token instanceof RegExp) {
                return token;
            }

            if (token.literal) {
                if (!token.literal.length) {
                    return null;
                }
                if (token.literal.length === 1 || result.config.lexer) {
                    return token;
                }
                return buildStringToken(ruleName, token, env);
            }
            if (token.token) {
                if (result.config.lexer) {
                    var name = token.token;
                    if (result.customTokens.indexOf(name) === -1) {
                        result.customTokens.push(name);
                    }
                    var expr = result.config.lexer + ".has(" + JSON.stringify(name) + ") ? {type: " + JSON.stringify(name) + "} : " + name;
                    return {token: "(" + expr + ")"};
                }
                return token;
            }

            if (token.subexpression) {
                return buildSubExpressionToken(ruleName, token, env);
            }

            if (token.ebnf) {
                return buildEBNFToken(ruleName, token, env);
            }

            if (token.macrocall) {
                return buildMacroCallToken(ruleName, token, env);
            }

            if (token.mixin) {
                if (env[token.mixin]) {
                    return buildToken(ruleName, env[token.mixin], env);
                } else {
                    throw new Error("Unbound variable: " + token.mixin);
                }
            }

            throw new Error("unrecognized token: " + JSON.stringify(token));
        }

        function buildStringToken(ruleName, token, env) {
            var newname = unique(ruleName + "$string");
            produceRules(newname, [
                {
                    tokens: token.literal.split("").map(function charLiteral(d) {
                        return {
                            literal: d
                        };
                    }),
                    postprocess: {builtin: "joiner"}
                }
            ], env);
            return newname;
        }

        function buildSubExpressionToken(ruleName, token, env) {
            var data = token.subexpression;
            var name = unique(ruleName + "$subexpression");
            //structure.push({"name": name, "rules": data});
            produceRules(name, data, env);
            return name;
        }

        function buildEBNFToken(ruleName, token, env) {
            switch (token.modifier) {
                case ":+":
                    return buildEBNFPlus(ruleName, token, env);
                case ":*":
                    return buildEBNFStar(ruleName, token, env);
                case ":?":
                    return buildEBNFOpt(ruleName, token, env);
            }
        }

        function buildEBNFPlus(ruleName, token, env) {
            var name = unique(ruleName + "$ebnf");
            /*
            structure.push({
                name: name,
                rules: [{
                    tokens: [token.ebnf],
                }, {
                    tokens: [token.ebnf, name],
                    postprocess: {builtin: "arrconcat"}
                }]
            });
            */
            produceRules(name,
                [{
                    tokens: [token.ebnf],
                }, {
                    tokens: [name, token.ebnf],
                    postprocess: {builtin: "arrpush"}
                }],
                env
            );
            return name;
        }

        function buildEBNFStar(ruleName, token, env) {
            var name = unique(ruleName + "$ebnf");
            /*
            structure.push({
                name: name,
                rules: [{
                    tokens: [],
                }, {
                    tokens: [token.ebnf, name],
                    postprocess: {builtin: "arrconcat"}
                }]
            });
            */
            produceRules(name,
                [{
                    tokens: [],
                }, {
                    tokens: [name, token.ebnf],
                    postprocess: {builtin: "arrpush"}
                }],
                env
            );
            return name;
        }

        function buildEBNFOpt(ruleName, token, env) {
            var name = unique(ruleName + "$ebnf");
            /*
            structure.push({
                name: name,
                rules: [{
                    tokens: [token.ebnf],
                    postprocess: {builtin: "id"}
                }, {
                    tokens: [],
                    postprocess: {builtin: "nuller"}
                }]
            });
            */
            produceRules(name,
                [{
                    tokens: [token.ebnf],
                    postprocess: {builtin: "id"}
                }, {
                    tokens: [],
                    postprocess: {builtin: "nuller"}
                }],
                env
            );
            return name;
        }

        function buildMacroCallToken(ruleName, token, env) {
            var name = unique(ruleName + "$macrocall");
            var macro = result.macros[token.macrocall];
            if (!macro) {
                throw new Error("Unkown macro: "+token.macrocall);
            }
            if (macro.args.length !== token.args.length) {
                throw new Error("Argument count mismatch.");
            }
            var newenv = {__proto__: env};
            for (var i=0; i<macro.args.length; i++) {
                var argrulename = unique(ruleName + "$macrocall");
                newenv[macro.args[i]] = argrulename;
                produceRules(argrulename, [token.args[i]], env);
                //structure.push({"name": argrulename, "rules":[token.args[i]]});
                //buildRule(name, token.args[i], env);
            }
            produceRules(name, macro.exprs, newenv);
            return name;
        }
    }

    function uniquer() {
        var uns = {};
        return unique;
        function unique(name) {
            var un = uns[name] = (uns[name] || 0) + 1;
            return name + '$' + un;
        }
    }

    return Compile;

}));

}).call(this)}).call(this,require('_process'),"/node_modules/nearley/lib")
},{"./nearley":5,"./nearley-language-bootstrapped.js":4,"_process":14,"fs":12,"path":13}],3:[function(require,module,exports){
(function(root, factory) {
    if (typeof module === 'object' && module.exports) {
        module.exports = factory(require('./nearley'));
    } else {
        root.generate = factory(root.nearley);
    }
}(this, function(nearley) {

    function serializeRules(rules, builtinPostprocessors, extraIndent) {
        if (extraIndent == null) {
            extraIndent = ''
        }

        return '[\n    ' + rules.map(function(rule) {
            return serializeRule(rule, builtinPostprocessors);
        }).join(',\n    ') + '\n' + extraIndent + ']';
    }

    function dedentFunc(func) {
        var lines = func.toString().split(/\n/);

        if (lines.length === 1) {
            return [lines[0].replace(/^\s+|\s+$/g, '')];
        }

        var indent = null;
        var tail = lines.slice(1);
        for (var i = 0; i < tail.length; i++) {
            var match = /^\s*/.exec(tail[i]);
            if (match && match[0].length !== tail[i].length) {
                if (indent === null ||
                    match[0].length < indent.length) {
                    indent = match[0];
                }
            }
        }

        if (indent === null) {
            return lines;
        }

        return lines.map(function dedent(line) {
            if (line.slice(0, indent.length) === indent) {
                return line.slice(indent.length);
            }
            return line;
        });
    }

    function tabulateString(string, indent, options) {
        var lines;
        if(Array.isArray(string)) {
          lines = string;
        } else {
          lines = string.toString().split('\n');
        }

        options = options || {};
        var tabulated = lines.map(function addIndent(line, i) {
            var shouldIndent = true;

            if(i == 0 && !options.indentFirst) {
              shouldIndent = false;
            }

            if(shouldIndent) {
                return indent + line;
            } else {
                return line;
            }
        }).join('\n');

        return tabulated;
    }

    function serializeSymbol(s) {
        if (s instanceof RegExp) {
            return s.toString();
        } else if (s.token) {
            return s.token;
        } else {
            return JSON.stringify(s);
        }
    }

    function serializeRule(rule, builtinPostprocessors) {
        var ret = '{';
        ret += '"name": ' + JSON.stringify(rule.name);
        ret += ', "symbols": [' + rule.symbols.map(serializeSymbol).join(', ') + ']';
        if (rule.postprocess) {
            if(rule.postprocess.builtin) {
                rule.postprocess = builtinPostprocessors[rule.postprocess.builtin];
            }
            ret += ', "postprocess": ' + tabulateString(dedentFunc(rule.postprocess), '        ', {indentFirst: false});
        }
        ret += '}';
        return ret;
    }

    var generate = function (parser, exportName) {
        if(!parser.config.preprocessor) {
            parser.config.preprocessor = "_default";
        }

        if(!generate[parser.config.preprocessor]) {
            throw new Error("No such preprocessor: " + parser.config.preprocessor)
        }

        return generate[parser.config.preprocessor](parser, exportName);
    };

    generate.js = generate._default = generate.javascript = function (parser, exportName) {
        var output = "// Generated automatically by nearley, version " + parser.version + "\n";
        output +=  "// http://github.com/Hardmath123/nearley\n";
        output += "(function () {\n";
        output += "function id(x) { return x[0]; }\n";
        output += parser.body.join('\n');
        output += "var grammar = {\n";
        output += "    Lexer: " + parser.config.lexer + ",\n";
        output += "    ParserRules: " +
            serializeRules(parser.rules, generate.javascript.builtinPostprocessors)
            + "\n";
        output += "  , ParserStart: " + JSON.stringify(parser.start) + "\n";
        output += "}\n";
        output += "if (typeof module !== 'undefined'"
            + "&& typeof module.exports !== 'undefined') {\n";
        output += "   module.exports = grammar;\n";
        output += "} else {\n";
        output += "   window." + exportName + " = grammar;\n";
        output += "}\n";
        output += "})();\n";
        return output;
    };

    generate.javascript.builtinPostprocessors = {
        "joiner": "function joiner(d) {return d.join('');}",
        "arrconcat": "function arrconcat(d) {return [d[0]].concat(d[1]);}",
        "arrpush": "function arrpush(d) {return d[0].concat([d[1]]);}",
        "nuller": "function(d) {return null;}",
        "id": "id"
    }

    generate.module = generate.esmodule = function (parser, exportName) {
        var output = "// Generated automatically by nearley, version " + parser.version + "\n";
        output +=  "// http://github.com/Hardmath123/nearley\n";
        output += "function id(x) { return x[0]; }\n";
        output += parser.body.join('\n');
        output += "let Lexer = " + parser.config.lexer + ";\n";
        output += "let ParserRules = " + serializeRules(parser.rules, generate.javascript.builtinPostprocessors) + ";\n";
        output += "let ParserStart = " + JSON.stringify(parser.start) + ";\n";
        output += "export default { Lexer, ParserRules, ParserStart };\n";
        return output;
    };

    generate.cs = generate.coffee = generate.coffeescript = function (parser, exportName) {
        var output = "# Generated automatically by nearley, version " + parser.version + "\n";
        output +=  "# http://github.com/Hardmath123/nearley\n";
        output += "do ->\n";
        output += "  id = (d) -> d[0]\n";
        output += tabulateString(dedentFunc(parser.body.join('\n')), '  ') + '\n';
        output += "  grammar = {\n";
        output += "    Lexer: " + parser.config.lexer + ",\n";
        output += "    ParserRules: " +
            tabulateString(
                    serializeRules(parser.rules, generate.coffeescript.builtinPostprocessors),
                    '      ',
                    {indentFirst: false})
        + ",\n";
        output += "    ParserStart: " + JSON.stringify(parser.start) + "\n";
        output += "  }\n";
        output += "  if typeof module != 'undefined' "
            + "&& typeof module.exports != 'undefined'\n";
        output += "    module.exports = grammar;\n";
        output += "  else\n";
        output += "    window." + exportName + " = grammar;\n";
        return output;
    };

    generate.coffeescript.builtinPostprocessors = {
        "joiner": "(d) -> d.join('')",
        "arrconcat": "(d) -> [d[0]].concat(d[1])",
        "arrpush": "(d) -> d[0].concat([d[1]])",
        "nuller": "() -> null",
        "id": "id"
    };

    generate.ts = generate.typescript = function (parser, exportName) {
        var output = "// Generated automatically by nearley, version " + parser.version + "\n";
        output +=  "// http://github.com/Hardmath123/nearley\n";
        output +=  "// Bypasses TS6133. Allow declared but unused functions.\n";
        output +=  "// @ts-ignore\n";
        output += "function id(d: any[]): any { return d[0]; }\n";
        output += parser.customTokens.map(function (token) { return "declare var " + token + ": any;\n" }).join("")
        output += parser.body.join('\n');
        output += "\n";
        output += "interface NearleyToken {\n";
        output += "  value: any;\n";
        output += "  [key: string]: any;\n";
        output += "};\n";
        output += "\n";
        output += "interface NearleyLexer {\n";
        output += "  reset: (chunk: string, info: any) => void;\n";
        output += "  next: () => NearleyToken | undefined;\n";
        output += "  save: () => any;\n";
        output += "  formatError: (token: never) => string;\n";
        output += "  has: (tokenType: string) => boolean;\n";
        output += "};\n";
        output += "\n";
        output += "interface NearleyRule {\n";
        output += "  name: string;\n";
        output += "  symbols: NearleySymbol[];\n";
        output += "  postprocess?: (d: any[], loc?: number, reject?: {}) => any;\n";
        output += "};\n";
        output += "\n";
        output += "type NearleySymbol = string | { literal: any } | { test: (token: any) => boolean };\n";
        output += "\n";
        output += "interface Grammar {\n";
        output += "  Lexer: NearleyLexer | undefined;\n";
        output += "  ParserRules: NearleyRule[];\n";
        output += "  ParserStart: string;\n";
        output += "};\n";
        output += "\n";
        output += "const grammar: Grammar = {\n";
        output += "  Lexer: " + parser.config.lexer + ",\n";
        output += "  ParserRules: " + serializeRules(parser.rules, generate.typescript.builtinPostprocessors, "  ") + ",\n";
        output += "  ParserStart: " + JSON.stringify(parser.start) + ",\n";
        output += "};\n";
        output += "\n";
        output += "export default grammar;\n";

        return output;
    };

    generate.typescript.builtinPostprocessors = {
        "joiner": "(d) => d.join('')",
        "arrconcat": "(d) => [d[0]].concat(d[1])",
        "arrpush": "(d) => d[0].concat([d[1]])",
        "nuller": "() => null",
        "id": "id"
    };

    return generate;

}));

},{"./nearley":5}],4:[function(require,module,exports){
// Generated automatically by nearley, version 2.19.5
// http://github.com/Hardmath123/nearley
(function () {
function id(x) { return x[0]; }

function getValue(d) {
    return d[0].value
}

function literals(list) {
    var rules = {}
    for (var lit of list) {
        rules[lit] = {match: lit, next: 'main'}
    }
    return rules
}

var moo = require('moo')
var rules = Object.assign({
    ws: {match: /\s+/, lineBreaks: true, next: 'main'},
    comment: /\#.*/,
    arrow: {match: /[=-]+\>/, next: 'main'},
    js: {
        match: /\{\%(?:[^%]|\%[^}])*\%\}/,
        value: x => x.slice(2, -2),
        lineBreaks: true,
    },
    word: {match: /[\w\?\+]+/, next: 'afterWord'},
    string: {
        match: /"(?:[^\\"\n]|\\["\\/bfnrt]|\\u[a-fA-F0-9]{4})*"/,
        value: x => JSON.parse(x),
        next: 'main',
    },
    btstring: {
        match: /`[^`]*`/,
        value: x => x.slice(1, -1),
        next: 'main',
        lineBreaks: true,
    },
}, literals([
    ",", "|", "$", "%", "(", ")",
    ":?", ":*", ":+",
    "@include", "@builtin", "@",
    "]",
]))

var lexer = moo.states({
    main: Object.assign({}, rules, {
        charclass: {
            match: /\.|\[(?:\\.|[^\\\n])+?\]/,
            value: x => new RegExp(x),
        },
    }),
    // Both macro arguments and charclasses are both enclosed in [ ].
    // We disambiguate based on whether the previous token was a `word`.
    afterWord: Object.assign({}, rules, {
        "[": {match: "[", next: 'main'},
    }),
})

function insensitive(sl) {
    var s = sl.literal;
    var result = [];
    for (var i=0; i<s.length; i++) {
        var c = s.charAt(i);
        if (c.toUpperCase() !== c || c.toLowerCase() !== c) {
            result.push(new RegExp("[" + c.toLowerCase() + c.toUpperCase() + "]"));
            } else {
            result.push({literal: c});
        }
    }
    return {subexpression: [{tokens: result, postprocess: function(d) {return d.join(""); }}]};
}

var grammar = {
    Lexer: lexer,
    ParserRules: [
    {"name": "final$ebnf$1", "symbols": [(lexer.has("ws") ? {type: "ws"} : ws)], "postprocess": id},
    {"name": "final$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "final", "symbols": ["_", "prog", "_", "final$ebnf$1"], "postprocess": function(d) { return d[1]; }},
    {"name": "prog", "symbols": ["prod"], "postprocess": function(d) { return [d[0]]; }},
    {"name": "prog", "symbols": ["prod", "ws", "prog"], "postprocess": function(d) { return [d[0]].concat(d[2]); }},
    {"name": "prod", "symbols": ["word", "_", (lexer.has("arrow") ? {type: "arrow"} : arrow), "_", "expression+"], "postprocess": function(d) { return {name: d[0], rules: d[4]}; }},
    {"name": "prod", "symbols": ["word", {"literal":"["}, "_", "wordlist", "_", {"literal":"]"}, "_", (lexer.has("arrow") ? {type: "arrow"} : arrow), "_", "expression+"], "postprocess": function(d) {return {macro: d[0], args: d[3], exprs: d[9]}}},
    {"name": "prod", "symbols": [{"literal":"@"}, "_", "js"], "postprocess": function(d) { return {body: d[2]}; }},
    {"name": "prod", "symbols": [{"literal":"@"}, "word", "ws", "word"], "postprocess": function(d) { return {config: d[1], value: d[3]}; }},
    {"name": "prod", "symbols": [{"literal":"@include"}, "_", "string"], "postprocess": function(d) {return {include: d[2].literal, builtin: false}}},
    {"name": "prod", "symbols": [{"literal":"@builtin"}, "_", "string"], "postprocess": function(d) {return {include: d[2].literal, builtin: true }}},
    {"name": "expression+", "symbols": ["completeexpression"]},
    {"name": "expression+", "symbols": ["expression+", "_", {"literal":"|"}, "_", "completeexpression"], "postprocess": function(d) { return d[0].concat([d[4]]); }},
    {"name": "expressionlist", "symbols": ["completeexpression"]},
    {"name": "expressionlist", "symbols": ["expressionlist", "_", {"literal":","}, "_", "completeexpression"], "postprocess": function(d) { return d[0].concat([d[4]]); }},
    {"name": "wordlist", "symbols": ["word"]},
    {"name": "wordlist", "symbols": ["wordlist", "_", {"literal":","}, "_", "word"], "postprocess": function(d) { return d[0].concat([d[4]]); }},
    {"name": "completeexpression", "symbols": ["expr"], "postprocess": function(d) { return {tokens: d[0]}; }},
    {"name": "completeexpression", "symbols": ["expr", "_", "js"], "postprocess": function(d) { return {tokens: d[0], postprocess: d[2]}; }},
    {"name": "expr_member", "symbols": ["word"], "postprocess": id},
    {"name": "expr_member", "symbols": [{"literal":"$"}, "word"], "postprocess": function(d) {return {mixin: d[1]}}},
    {"name": "expr_member", "symbols": ["word", {"literal":"["}, "_", "expressionlist", "_", {"literal":"]"}], "postprocess": function(d) {return {macrocall: d[0], args: d[3]}}},
    {"name": "expr_member$ebnf$1", "symbols": [{"literal":"i"}], "postprocess": id},
    {"name": "expr_member$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "expr_member", "symbols": ["string", "expr_member$ebnf$1"], "postprocess": function(d) { if (d[1]) {return insensitive(d[0]); } else {return d[0]; } }},
    {"name": "expr_member", "symbols": [{"literal":"%"}, "word"], "postprocess": function(d) {return {token: d[1]}}},
    {"name": "expr_member", "symbols": ["charclass"], "postprocess": id},
    {"name": "expr_member", "symbols": [{"literal":"("}, "_", "expression+", "_", {"literal":")"}], "postprocess": function(d) {return {'subexpression': d[2]} ;}},
    {"name": "expr_member", "symbols": ["expr_member", "_", "ebnf_modifier"], "postprocess": function(d) {return {'ebnf': d[0], 'modifier': d[2]}; }},
    {"name": "ebnf_modifier", "symbols": [{"literal":":+"}], "postprocess": getValue},
    {"name": "ebnf_modifier", "symbols": [{"literal":":*"}], "postprocess": getValue},
    {"name": "ebnf_modifier", "symbols": [{"literal":":?"}], "postprocess": getValue},
    {"name": "expr", "symbols": ["expr_member"]},
    {"name": "expr", "symbols": ["expr", "ws", "expr_member"], "postprocess": function(d){ return d[0].concat([d[2]]); }},
    {"name": "word", "symbols": [(lexer.has("word") ? {type: "word"} : word)], "postprocess": getValue},
    {"name": "string", "symbols": [(lexer.has("string") ? {type: "string"} : string)], "postprocess": d => ({literal: d[0].value})},
    {"name": "string", "symbols": [(lexer.has("btstring") ? {type: "btstring"} : btstring)], "postprocess": d => ({literal: d[0].value})},
    {"name": "charclass", "symbols": [(lexer.has("charclass") ? {type: "charclass"} : charclass)], "postprocess": getValue},
    {"name": "js", "symbols": [(lexer.has("js") ? {type: "js"} : js)], "postprocess": getValue},
    {"name": "_$ebnf$1", "symbols": ["ws"], "postprocess": id},
    {"name": "_$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "_", "symbols": ["_$ebnf$1"]},
    {"name": "ws", "symbols": [(lexer.has("ws") ? {type: "ws"} : ws)]},
    {"name": "ws$ebnf$1", "symbols": [(lexer.has("ws") ? {type: "ws"} : ws)], "postprocess": id},
    {"name": "ws$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "ws", "symbols": ["ws$ebnf$1", (lexer.has("comment") ? {type: "comment"} : comment), "_"]}
]
  , ParserStart: "final"
}
if (typeof module !== 'undefined'&& typeof module.exports !== 'undefined') {
   module.exports = grammar;
} else {
   window.grammar = grammar;
}
})();

},{"moo":1}],5:[function(require,module,exports){
(function(root, factory) {
    if (typeof module === 'object' && module.exports) {
        module.exports = factory();
    } else {
        root.nearley = factory();
    }
}(this, function() {

    function Rule(name, symbols, postprocess) {
        this.id = ++Rule.highestId;
        this.name = name;
        this.symbols = symbols;        // a list of literal | regex class | nonterminal
        this.postprocess = postprocess;
        return this;
    }
    Rule.highestId = 0;

    Rule.prototype.toString = function(withCursorAt) {
        var symbolSequence = (typeof withCursorAt === "undefined")
                             ? this.symbols.map(getSymbolShortDisplay).join(' ')
                             : (   this.symbols.slice(0, withCursorAt).map(getSymbolShortDisplay).join(' ')
                                 + " ● "
                                 + this.symbols.slice(withCursorAt).map(getSymbolShortDisplay).join(' ')     );
        return this.name + " → " + symbolSequence;
    }


    // a State is a rule at a position from a given starting point in the input stream (reference)
    function State(rule, dot, reference, wantedBy) {
        this.rule = rule;
        this.dot = dot;
        this.reference = reference;
        this.data = [];
        this.wantedBy = wantedBy;
        this.isComplete = this.dot === rule.symbols.length;
    }

    State.prototype.toString = function() {
        return "{" + this.rule.toString(this.dot) + "}, from: " + (this.reference || 0);
    };

    State.prototype.nextState = function(child) {
        var state = new State(this.rule, this.dot + 1, this.reference, this.wantedBy);
        state.left = this;
        state.right = child;
        if (state.isComplete) {
            state.data = state.build();
            // Having right set here will prevent the right state and its children
            // form being garbage collected
            state.right = undefined;
        }
        return state;
    };

    State.prototype.build = function() {
        var children = [];
        var node = this;
        do {
            children.push(node.right.data);
            node = node.left;
        } while (node.left);
        children.reverse();
        return children;
    };

    State.prototype.finish = function() {
        if (this.rule.postprocess) {
            this.data = this.rule.postprocess(this.data, this.reference, Parser.fail);
        }
    };


    function Column(grammar, index) {
        this.grammar = grammar;
        this.index = index;
        this.states = [];
        this.wants = {}; // states indexed by the non-terminal they expect
        this.scannable = []; // list of states that expect a token
        this.completed = {}; // states that are nullable
    }


    Column.prototype.process = function(nextColumn) {
        var states = this.states;
        var wants = this.wants;
        var completed = this.completed;

        for (var w = 0; w < states.length; w++) { // nb. we push() during iteration
            var state = states[w];

            if (state.isComplete) {
                state.finish();
                if (state.data !== Parser.fail) {
                    // complete
                    var wantedBy = state.wantedBy;
                    for (var i = wantedBy.length; i--; ) { // this line is hot
                        var left = wantedBy[i];
                        this.complete(left, state);
                    }

                    // special-case nullables
                    if (state.reference === this.index) {
                        // make sure future predictors of this rule get completed.
                        var exp = state.rule.name;
                        (this.completed[exp] = this.completed[exp] || []).push(state);
                    }
                }

            } else {
                // queue scannable states
                var exp = state.rule.symbols[state.dot];
                if (typeof exp !== 'string') {
                    this.scannable.push(state);
                    continue;
                }

                // predict
                if (wants[exp]) {
                    wants[exp].push(state);

                    if (completed.hasOwnProperty(exp)) {
                        var nulls = completed[exp];
                        for (var i = 0; i < nulls.length; i++) {
                            var right = nulls[i];
                            this.complete(state, right);
                        }
                    }
                } else {
                    wants[exp] = [state];
                    this.predict(exp);
                }
            }
        }
    }

    Column.prototype.predict = function(exp) {
        var rules = this.grammar.byName[exp] || [];

        for (var i = 0; i < rules.length; i++) {
            var r = rules[i];
            var wantedBy = this.wants[exp];
            var s = new State(r, 0, this.index, wantedBy);
            this.states.push(s);
        }
    }

    Column.prototype.complete = function(left, right) {
        var copy = left.nextState(right);
        this.states.push(copy);
    }


    function Grammar(rules, start) {
        this.rules = rules;
        this.start = start || this.rules[0].name;
        var byName = this.byName = {};
        this.rules.forEach(function(rule) {
            if (!byName.hasOwnProperty(rule.name)) {
                byName[rule.name] = [];
            }
            byName[rule.name].push(rule);
        });
    }

    // So we can allow passing (rules, start) directly to Parser for backwards compatibility
    Grammar.fromCompiled = function(rules, start) {
        var lexer = rules.Lexer;
        if (rules.ParserStart) {
          start = rules.ParserStart;
          rules = rules.ParserRules;
        }
        var rules = rules.map(function (r) { return (new Rule(r.name, r.symbols, r.postprocess)); });
        var g = new Grammar(rules, start);
        g.lexer = lexer; // nb. storing lexer on Grammar is iffy, but unavoidable
        return g;
    }


    function StreamLexer() {
      this.reset("");
    }

    StreamLexer.prototype.reset = function(data, state) {
        this.buffer = data;
        this.index = 0;
        this.line = state ? state.line : 1;
        this.lastLineBreak = state ? -state.col : 0;
    }

    StreamLexer.prototype.next = function() {
        if (this.index < this.buffer.length) {
            var ch = this.buffer[this.index++];
            if (ch === '\n') {
              this.line += 1;
              this.lastLineBreak = this.index;
            }
            return {value: ch};
        }
    }

    StreamLexer.prototype.save = function() {
      return {
        line: this.line,
        col: this.index - this.lastLineBreak,
      }
    }

    StreamLexer.prototype.formatError = function(token, message) {
        // nb. this gets called after consuming the offending token,
        // so the culprit is index-1
        var buffer = this.buffer;
        if (typeof buffer === 'string') {
            var lines = buffer
                .split("\n")
                .slice(
                    Math.max(0, this.line - 5), 
                    this.line
                );

            var nextLineBreak = buffer.indexOf('\n', this.index);
            if (nextLineBreak === -1) nextLineBreak = buffer.length;
            var col = this.index - this.lastLineBreak;
            var lastLineDigits = String(this.line).length;
            message += " at line " + this.line + " col " + col + ":\n\n";
            message += lines
                .map(function(line, i) {
                    return pad(this.line - lines.length + i + 1, lastLineDigits) + " " + line;
                }, this)
                .join("\n");
            message += "\n" + pad("", lastLineDigits + col) + "^\n";
            return message;
        } else {
            return message + " at index " + (this.index - 1);
        }

        function pad(n, length) {
            var s = String(n);
            return Array(length - s.length + 1).join(" ") + s;
        }
    }

    function Parser(rules, start, options) {
        if (rules instanceof Grammar) {
            var grammar = rules;
            var options = start;
        } else {
            var grammar = Grammar.fromCompiled(rules, start);
        }
        this.grammar = grammar;

        // Read options
        this.options = {
            keepHistory: false,
            lexer: grammar.lexer || new StreamLexer,
        };
        for (var key in (options || {})) {
            this.options[key] = options[key];
        }

        // Setup lexer
        this.lexer = this.options.lexer;
        this.lexerState = undefined;

        // Setup a table
        var column = new Column(grammar, 0);
        var table = this.table = [column];

        // I could be expecting anything.
        column.wants[grammar.start] = [];
        column.predict(grammar.start);
        // TODO what if start rule is nullable?
        column.process();
        this.current = 0; // token index
    }

    // create a reserved token for indicating a parse fail
    Parser.fail = {};

    Parser.prototype.feed = function(chunk) {
        var lexer = this.lexer;
        lexer.reset(chunk, this.lexerState);

        var token;
        while (true) {
            try {
                token = lexer.next();
                if (!token) {
                    break;
                }
            } catch (e) {
                // Create the next column so that the error reporter
                // can display the correctly predicted states.
                var nextColumn = new Column(this.grammar, this.current + 1);
                this.table.push(nextColumn);
                var err = new Error(this.reportLexerError(e));
                err.offset = this.current;
                err.token = e.token;
                throw err;
            }
            // We add new states to table[current+1]
            var column = this.table[this.current];

            // GC unused states
            if (!this.options.keepHistory) {
                delete this.table[this.current - 1];
            }

            var n = this.current + 1;
            var nextColumn = new Column(this.grammar, n);
            this.table.push(nextColumn);

            // Advance all tokens that expect the symbol
            var literal = token.text !== undefined ? token.text : token.value;
            var value = lexer.constructor === StreamLexer ? token.value : token;
            var scannable = column.scannable;
            for (var w = scannable.length; w--; ) {
                var state = scannable[w];
                var expect = state.rule.symbols[state.dot];
                // Try to consume the token
                // either regex or literal
                if (expect.test ? expect.test(value) :
                    expect.type ? expect.type === token.type
                                : expect.literal === literal) {
                    // Add it
                    var next = state.nextState({data: value, token: token, isToken: true, reference: n - 1});
                    nextColumn.states.push(next);
                }
            }

            // Next, for each of the rules, we either
            // (a) complete it, and try to see if the reference row expected that
            //     rule
            // (b) predict the next nonterminal it expects by adding that
            //     nonterminal's start state
            // To prevent duplication, we also keep track of rules we have already
            // added

            nextColumn.process();

            // If needed, throw an error:
            if (nextColumn.states.length === 0) {
                // No states at all! This is not good.
                var err = new Error(this.reportError(token));
                err.offset = this.current;
                err.token = token;
                throw err;
            }

            // maybe save lexer state
            if (this.options.keepHistory) {
              column.lexerState = lexer.save()
            }

            this.current++;
        }
        if (column) {
          this.lexerState = lexer.save()
        }

        // Incrementally keep track of results
        this.results = this.finish();

        // Allow chaining, for whatever it's worth
        return this;
    };

    Parser.prototype.reportLexerError = function(lexerError) {
        var tokenDisplay, lexerMessage;
        // Planning to add a token property to moo's thrown error
        // even on erroring tokens to be used in error display below
        var token = lexerError.token;
        if (token) {
            tokenDisplay = "input " + JSON.stringify(token.text[0]) + " (lexer error)";
            lexerMessage = this.lexer.formatError(token, "Syntax error");
        } else {
            tokenDisplay = "input (lexer error)";
            lexerMessage = lexerError.message;
        }
        return this.reportErrorCommon(lexerMessage, tokenDisplay);
    };

    Parser.prototype.reportError = function(token) {
        var tokenDisplay = (token.type ? token.type + " token: " : "") + JSON.stringify(token.value !== undefined ? token.value : token);
        var lexerMessage = this.lexer.formatError(token, "Syntax error");
        return this.reportErrorCommon(lexerMessage, tokenDisplay);
    };

    Parser.prototype.reportErrorCommon = function(lexerMessage, tokenDisplay) {
        var lines = [];
        lines.push(lexerMessage);
        var lastColumnIndex = this.table.length - 2;
        var lastColumn = this.table[lastColumnIndex];
        var expectantStates = lastColumn.states
            .filter(function(state) {
                var nextSymbol = state.rule.symbols[state.dot];
                return nextSymbol && typeof nextSymbol !== "string";
            });

        if (expectantStates.length === 0) {
            lines.push('Unexpected ' + tokenDisplay + '. I did not expect any more input. Here is the state of my parse table:\n');
            this.displayStateStack(lastColumn.states, lines);
        } else {
            lines.push('Unexpected ' + tokenDisplay + '. Instead, I was expecting to see one of the following:\n');
            // Display a "state stack" for each expectant state
            // - which shows you how this state came to be, step by step.
            // If there is more than one derivation, we only display the first one.
            var stateStacks = expectantStates
                .map(function(state) {
                    return this.buildFirstStateStack(state, []) || [state];
                }, this);
            // Display each state that is expecting a terminal symbol next.
            stateStacks.forEach(function(stateStack) {
                var state = stateStack[0];
                var nextSymbol = state.rule.symbols[state.dot];
                var symbolDisplay = this.getSymbolDisplay(nextSymbol);
                lines.push('A ' + symbolDisplay + ' based on:');
                this.displayStateStack(stateStack, lines);
            }, this);
        }
        lines.push("");
        return lines.join("\n");
    }
    
    Parser.prototype.displayStateStack = function(stateStack, lines) {
        var lastDisplay;
        var sameDisplayCount = 0;
        for (var j = 0; j < stateStack.length; j++) {
            var state = stateStack[j];
            var display = state.rule.toString(state.dot);
            if (display === lastDisplay) {
                sameDisplayCount++;
            } else {
                if (sameDisplayCount > 0) {
                    lines.push('    ^ ' + sameDisplayCount + ' more lines identical to this');
                }
                sameDisplayCount = 0;
                lines.push('    ' + display);
            }
            lastDisplay = display;
        }
    };

    Parser.prototype.getSymbolDisplay = function(symbol) {
        return getSymbolLongDisplay(symbol);
    };

    /*
    Builds a the first state stack. You can think of a state stack as the call stack
    of the recursive-descent parser which the Nearley parse algorithm simulates.
    A state stack is represented as an array of state objects. Within a
    state stack, the first item of the array will be the starting
    state, with each successive item in the array going further back into history.

    This function needs to be given a starting state and an empty array representing
    the visited states, and it returns an single state stack.

    */
    Parser.prototype.buildFirstStateStack = function(state, visited) {
        if (visited.indexOf(state) !== -1) {
            // Found cycle, return null
            // to eliminate this path from the results, because
            // we don't know how to display it meaningfully
            return null;
        }
        if (state.wantedBy.length === 0) {
            return [state];
        }
        var prevState = state.wantedBy[0];
        var childVisited = [state].concat(visited);
        var childResult = this.buildFirstStateStack(prevState, childVisited);
        if (childResult === null) {
            return null;
        }
        return [state].concat(childResult);
    };

    Parser.prototype.save = function() {
        var column = this.table[this.current];
        column.lexerState = this.lexerState;
        return column;
    };

    Parser.prototype.restore = function(column) {
        var index = column.index;
        this.current = index;
        this.table[index] = column;
        this.table.splice(index + 1);
        this.lexerState = column.lexerState;

        // Incrementally keep track of results
        this.results = this.finish();
    };

    // nb. deprecated: use save/restore instead!
    Parser.prototype.rewind = function(index) {
        if (!this.options.keepHistory) {
            throw new Error('set option `keepHistory` to enable rewinding')
        }
        // nb. recall column (table) indicies fall between token indicies.
        //        col 0   --   token 0   --   col 1
        this.restore(this.table[index]);
    };

    Parser.prototype.finish = function() {
        // Return the possible parsings
        var considerations = [];
        var start = this.grammar.start;
        var column = this.table[this.table.length - 1]
        column.states.forEach(function (t) {
            if (t.rule.name === start
                    && t.dot === t.rule.symbols.length
                    && t.reference === 0
                    && t.data !== Parser.fail) {
                considerations.push(t);
            }
        });
        return considerations.map(function(c) {return c.data; });
    };

    function getSymbolLongDisplay(symbol) {
        var type = typeof symbol;
        if (type === "string") {
            return symbol;
        } else if (type === "object") {
            if (symbol.literal) {
                return JSON.stringify(symbol.literal);
            } else if (symbol instanceof RegExp) {
                return 'character matching ' + symbol;
            } else if (symbol.type) {
                return symbol.type + ' token';
            } else if (symbol.test) {
                return 'token matching ' + String(symbol.test);
            } else {
                throw new Error('Unknown symbol type: ' + symbol);
            }
        }
    }

    function getSymbolShortDisplay(symbol) {
        var type = typeof symbol;
        if (type === "string") {
            return symbol;
        } else if (type === "object") {
            if (symbol.literal) {
                return JSON.stringify(symbol.literal);
            } else if (symbol instanceof RegExp) {
                return symbol.toString();
            } else if (symbol.type) {
                return '%' + symbol.type;
            } else if (symbol.test) {
                return '<' + String(symbol.test) + '>';
            } else {
                throw new Error('Unknown symbol type: ' + symbol);
            }
        }
    }

    return {
        Parser: Parser,
        Grammar: Grammar,
        Rule: Rule,
    };

}));

},{}],6:[function(require,module,exports){
const moo = require("moo");
const {MM, Compressor, Decompressor} = require("./metamath.js");

class Lexer {
  constructor() {
    const lexicon = {
      ["comment-expr"]: {match: /\/\*\*.*\*\//, lineBreaks: true},
      ["comment"]: {match: /\/\/.*\n/, lineBreaks: true},
      ["ws"]: {match: /[\s]+/, lineBreaks: true},
      ["_include_"]: "include",
      //["const"]: "const",
      //["var"]: "var",
      ["theorem"]: "theorem",
      ["axiom"]: "axiom",
      ["proof"]: "proof",
      ["end"]: "end",
      ["param"]: "param",
      ["let"]: "let",
      ["step"]: "step",
      ["assume"]: "assume",
      ["disjoint"]: "disjoint",
      ["assert"]: "assert",
      ["("]: "(",
      [")"]: ")",
      ['"']: '"',
      [":"]: ":",
      [","]: ",",
      [";"]: ";",
      ["@"]: "@",
      ["#"]: "#",
      ["label"]: /[A-Za-z0-9-_.]+/,
      ["sequence"]: /[!-#%-~\?]+/,
    };
    this.lexer = moo.compile(lexicon);
  }
  parse(code) {
    this.lexer.reset(code);
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


const symbols = [
  // a subset of possible symbols
  "label",
  // reserved keywords that can also be symbols
  '"',
  "(",
  ")",
  ",",
  ":",
  ";",
  "@",
  "#",
  "//",
  // catch all types of sequences
  "sequence",
];

const labels = [
  // a subset of possible labels
  "label",
  // reserved keywords that can also be labels
  "_include_",
  // "const",
  // "var",
  "theorem",
  "axiom",
  "proof",
  //"end",
  "let",
  "param",
  "step",
  "assume",
  "disjoint",
  "assert",
  // catch all types of sequences
];

class Parser {
  constructor() {
    this.lexer = new Lexer();
  }
  parse(code) {
    this.lexer.parse(code);
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
    const {line, col} = this.lexer.lexer;
    throw new Error(`Unexpected token "${head[1]}" (${head[0]}) on line ${line} column ${col}.`);
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
  
  ws(optional = false) {
    const sp = ["ws", "comment", "comment-expr"];
    // const sp = ["ws"];
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

  declaration(type, label = true, multiple = true, empty = true) {
    const result = [];
    this.eat(type);
    this.ws();
    if (label) {
      result.push(this. label());
      this.ws(true);
      this.eat(":");
      this.ws(true);
    }
    let first = this.symbol();
    result.push(first);
    this.ws(false);
    if (!this.accepts(...symbols) && empty) {
      // If empty symbols are allowed
      result.push("");
      return [type, result];
    }
    let second = this.symbol();
    //console.log(second);
    result.push(second);
    this.ws(false);
    if (multiple) {
      while (this.accepts(...symbols)) {
        result.push(this.symbol());
        this.ws(false);
      };
    }
    return [type, result];
  }

  axiom() {
    this.eat("axiom");
    this.ws();
    let name = this.label();
    this.ws();
    let h = this.header();
    this.eat("end");
    this.ws();
    return ["axiom", name, h];
  }
  
  header() {
    this.ws(true);
    let params = [];
    while (this.accepts("param")) {
      params.push(this.declaration("param", true, false));
    }
    
    this.ws(true);
    let lets = [];
    while (this.accepts("let")) {
      lets.push(this.declaration("let", true, false));
    }
    
    this.ws(true);
    let ifs = [];
    while (this.accepts("assume")) {
      ifs.push(this.declaration("assume", true, true));
    }

    this.ws(true);
    let disjoints = [];
    while (this.accepts("disjoint")) {
      disjoints.push(this.declaration("disjoint", false, true));
    }
    
    this.ws(true);
    let then = this.declaration("assert", false, true);

    return [params, lets, ifs, disjoints, then];
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
  
  step() {
    const result = [];
    this.eat("step");
    this.eat("ws");
    // index
    result.push(this.label());
    this.ws(true);
    this.eat(")");
    this.ws(true);
    // a step can either be ...
    if (this.accepts("#")) {
      // ... a marker ...
      result.push(this.eat("#"));
    } else if (this.accepts("@")) {
      // ... a recall ...
      result.push(this.eat("@"));
      result.push(this.label());
    } else {
      // ... or call.
      result.push(this.label());
      result.push(this.args());
    }
    this.ws(true);
    this.eat(":");
    this.ws(true);
    let sequence = [];
    result.push(sequence);
    while (this.accepts(...symbols)) {
      sequence.push(this.symbol());
      this.ws(true);
    }
    return result;
  }

  symbol() {
    let name = this.eat(...symbols);
    while (this.accepts(...symbols)) {
      name += this.eat(...symbols);
    }
    return name;
  }
  
  label() {
    let name = this.eat(...labels);
    while (this.accepts(...labels)) {
      name += this.eat(...labels);
    }
    return name;
  }
  
  theorem() {
    this.eat("theorem");
    this.ws();

    let name = this.label();
    this.ws();
    let head = this.header();

    this.ws(true);
    this.eat("proof");
    this.ws(true);
    
    let steps = [];
    do {
      if (this.accepts(...labels)) {
        steps.push(this.label());
      } else if (this.accepts("#")) {
        steps.push(this.eat("#"));
      } else if (this.accepts("@")) {
        steps.push(`${this.eat("@")}${this.label()}`);
      } else {
        break;
      }
      this.ws();
    } while (true);

    this.eat("end");
    this.ws();

    return ["theorem", name, head, steps];
  }
  
  include() {
    this.eat("_include_");
    this.ws();
    this.eat('"');
    const name = this.eat("label");
    this.eat('"');
    this.ws();
    return ["include", name];
  }
    
  top() {
    this.lexer.next();
    let result = [];
    do {
      if (this.accepts("ws")) {
        this.ws();
      } else if (this.accepts("//")) {
        throw new Error("hi");
      } else if (this.accepts("axiom")) {
        result.push(this.axiom());
      } else if (this.accepts("theorem")) {
        result.push(this.theorem());
      } else if (this.accepts("_include_")) {
        result.push(this.include());
      } else {
        this.error();
      }
      // console.log(this.lexer.head);
    } while (this.lexer.head);
    // throw new Error("hi");
    return result;
  }
}

class Compiler {
  constructor(loader) {
    this.load = loader;
  }
  async preprocess(dir, file) {
    const queue = [file];

    const files = {};
    
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

  async compile(dirOrSource, file) {
    if (!file) {
      let parser = new Parser();
      let code = parser.parse(dirOrSource);
      return this.transpile(code);
    }
    const files = await this.preprocess(dirOrSource, file);
    const dump = Object.values(files)
          .flat()
          .filter(([type]) => type != "include");
    return this.transpile(dump);
  }

  transpile(code) {
    //console.log(code);
    //throw new Error();

    //console.log(code);
    
    const consts = new Set();
    for (let [type, label, [vars, dummies, assumes, disjoints, [, assert]], proof] of code) {
      // All variable types are constants
      for (let type of vars.map(([, [label, type, name]]) => type)) {
        consts.add(type);
      }

      const names = vars.map(([, [label, type, name]]) => name);

      // All symbols in logical hypothesis that aren't variables are constants
      const logical = [...assumes]
            .map(([, [type, ...symbols]]) => [type, symbols])
            .map(([type, symbols]) => symbols.filter((symbol) => !names.includes(symbol)))
            .flat();
      for (let symbol of logical) {
        consts.add(symbol);
      }
      // All symbols in assertions that aren't variables are constants
      for (let symbol of assert.filter((symbol) => !names.includes(symbol))) {
        consts.add(symbol);
      }
    }

    let result = [];
    result.push(`$c ${[...consts].join(" ")} $.`);

    for (let [type, label, [vars, dummies, assumes, disjoints, [, assert]], proof] of code) {

      const names = [...vars, ...dummies].map(([, [label, type, name]]) => name);

      const mandatory = new Set();

      for (const hyp of [...JSON.parse(JSON.stringify(assumes)).map(([, string]) => string.splice(1)), assert]) {
        for (const tok of hyp) {
          if (names.includes(tok)) {
            mandatory.add(tok);
          } else if (!consts.has(tok)) {
            throw new Error(`Undeclared token: "${tok}" is neither a constant nor a variable.`);
          }
        }
      }

      // console.log(mandatory);
      
      const types = [...vars, ...dummies].map(([, [label, type, name]]) => `  ${label} $f ${type} ${name} $.`);
      //console.log(assumes);
      const logical = [...JSON.parse(JSON.stringify(assumes))]
            .map(([, assumption]) => [assumption.shift(), assumption.shift(), assumption])
            .map(([label, type, symbols]) => `  ${label} $e ${type} ${symbols.join(" ")} $.`);
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
          //console.log(f);
          //throw new Error("hi");
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
  ${label} $${type == "axiom" ? "a" : "p"} ${assert.join(" ")} ${p}$.
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
    let args = f.map(([type, name, label]) => `  param ${label}: ${type} ${name}`).join("\n");
    if (Object.entries(f).length  > 0) {
      args += "\n";
    }
    
    let assumptions = e.map(([seq, type, name]) => `  assume ${name}: ${type} ${seq.join(" ")}`).join("\n");

    if (Object.entries(e).length > 0) {
      assumptions += "\n";
    }

    const result = `
axiom ${label}
${args}${assumptions}  assert ${type} ${axiom.join(' ')}
end
`;

    return [[], result];
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

    const varz = [];

    for (const [type, name, label] of f) {
      varz.push(`  param ${label}: ${type} ${name}`);
    }
    
    for (const [type, name, label] of dummies) {
      varz.push(`  let ${label}: ${type} ${name}`);
    }

    const args = varz.join("\n");
    
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
    
    let assumptions = e.map(([seq, type, name]) => `  assume ${name}: ${type} ${seq.join(" ")}`).join("\n");

    if (Object.entries(e).length > 0) {
      assumptions += "\n";
    }
    
    let diff = [];
    for (let [x, y] of d) {
      diff.push(`  disjoint ${x} ${y}`);
    }
    
    for (let [x, y] of ddummy) {
      diff.push(`  disjoint ${x} ${y}`);
    }
    
    const body = steps.map((step, i) => {
      const call = typeof step == "number" ? (step == -1 ? `#` : `@${step}`) : `${step}`;
      return `    ${call}`;
    }).join("\n");
    
    const code = `
theorem ${label}
${args}
${assumptions}
${d.length > 0 ? diff.join("\n") : ""}
  assert ${type} ${theorem.join(' ')}

  proof
${body}
end
`;

    return [deps, code];
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

},{"../src/descent.js":7,"./metamath.js":9,"moo":1}],7:[function(require,module,exports){
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
    do {
      symbols.push(this.eat("sequence"));
      this.space();
    } while (this.accepts("sequence"));
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
  verify(program) {
    let proofs = 0;
    let mm = process(program);
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

},{"../src/lexer.js":8,"../src/metamath.js":9,"moo":1}],8:[function(require,module,exports){
const moo = require("moo");

const lexicon = {
  comment: {match: /\$\([\s]+(?:(?!\$\))[\s\S])*\$\)/, lineBreaks: true},
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
  //lparen: "(",
  //rparen: ")",
  ws: {match: /[\s]+/, lineBreaks: true},
  sequence: /[!-#%-~\?]+/,
  // letter_or_digit: /[A-Za-z0-9]/,
  // symbol: /[!-#%-~]+/,
};

const lexer = moo.compile(lexicon);

module.exports = {
  lexicon: lexicon,
  lexer: lexer
};

},{"moo":1}],9:[function(require,module,exports){
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
        markers.push(top);
        steps.push([step, top.slice(1)]);
        continue;
      } else if (typeof step == "number") {
        // Takes a prior computation, which was already
        // previously verified (since it was at the top of
        // the stack at some point), and reuses its result
        // in another computation by pushing it into the stack.
        stack.push(markers[step]);
        steps.push([step, markers[step].slice(1)]);
        continue;
      }
      
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
              console.log(`  ${type} ${string.flat().join(" ")}`);
            }
            // console.log(mandatory);
            throw new Error(`Step "${step}" of "${label}": argument type of "${v}" doesn't match with the top of the stack. Expected "${k}" but got "${top[1]}".`);
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
            const e = [];
            e.push(`Substitution ${JSON.stringify(subs)} of the hypothesis ${h.join(" ")} doesn't match with the top of the stack`);
            e.push(`Step ${step}: Expected ${sub.flat().join("")} but got ${top[2].join("")}.`);
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

},{}],10:[function(require,module,exports){
const parser = require("./parser.js");
const metamath = require("./metamath.js");
const descent = require("./descent.js");
const compiler = require("./compiler.js");

module.exports = {
  parser: parser,
  metamath: metamath,
  descent: descent,
  compiler: compiler,
};

},{"./compiler.js":6,"./descent.js":7,"./metamath.js":9,"./parser.js":11}],11:[function(require,module,exports){
const nearley = require("nearley");
const compile = require("nearley/lib/compile");
const generate = require("nearley/lib/generate");
const nearleyGrammar = require("nearley/lib/nearley-language-bootstrapped");

const {lexer} = require("./lexer.js");

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

//const handler = true;

const grammar = (handler) => compileGrammar(handler, `
      @lexer lexer

      #database -> _ outermost_scope_stmt (__ outermost_scope_stmt):* _ {% ([ws1, stmt, list, ws2]) =>
      #  [stmt].concat(list.map(([ws, v]) => v)) 
      #%}

      database -> _ __aline_plus _ {% ([ws, lines]) => lines %}

      __aline_plus -> outermost_scope_stmt {%
            ([line]) => {
              if (handler) {
                handler.feed([line]);
                return null;
              }
              return [line];
            }
           %} |
           __aline_plus __ outermost_scope_stmt {%
             ([prior, ws, next]) => {
               if (handler) {
                 handler.feed([next]);
                 return null;
               }
               return [...prior, next];
             }
          %}

      outermost_scope_stmt -> include_stmt {% id %} | 
                              constant_stmt {% id %} | 
                              stmt {% id %}

      # File inclusion command; process file as a database.
      # Databases should NOT have a comment in the filename.
      include_stmt -> %lfile  __ filename __ %rfile {% ([b1, ws1, f, ws2, b2]) => [b1.text, f.text, b2.text] %}

      # Constant symbols declaration.
      constant_stmt -> %c __ constant (__ constant):* __ %dot {% ([c, ws1, cons, list, ws2, d]) => 
        [c.text, [cons.text].concat(list.map(([ws, v]) => v.text)), d.text]
      %}

      # A normal statement can occur in any scope.
      stmt -> block {% id %} | 
              variable_stmt {% id %} | 
              disjoint_stmt {% id %} |
              hypothesis_stmt {% id %} | 
              assert_stmt {% id %}

      # A block. You can have 0 statements in a block.
      block -> %lscope (__ stmt):* __ %rscope {% ([b1, list, ws, b2]) => 
        [b1.text, list.map(([ws, v]) => v), b2.text] 
      %}

      # Variable symbols declaration.
      variable_stmt -> %v __ variable (__ variable):* __ %dot {% ([v, ws1, a, list, ws2, d]) => 
        [v.text, [a.text].concat(list.map(([ws, arg]) => arg.text)), d.text] 
      %}

      # Disjoint variables. Simple disjoint statements have
      # 2 variables, i.e., "variable*" is empty for them.
      disjoint_stmt -> %d __ variable (__ variable):* __ %dot {% ([v, ws1, a, list, ws2, d]) =>
        [v.text, [a.text].concat(list.map(([ws, arg]) => arg.text)), d.text]
      %}

      hypothesis_stmt -> floating_stmt {% id %} | essential_stmt {% id %}

      # Floating (variable-type) hypothesis.
      floating_stmt -> LABEL __ %f __ typecode __ variable __ %dot {% ([l, ws1, f, ws2, t, ws3, v, ws4, d]) => [l, f.text, t.text, v.text, d.text] %}

      # Essential (logical) hypothesis.
      essential_stmt -> LABEL __ %e __ typecode (__ MATH_SYMBOL):* __ %dot {% ([l, ws1, e, ws2, t, list, ws4, d]) => 
        [l, e.text, t.text, list.map(([ws, v]) => v.text), d.text] 
      %}

      assert_stmt -> axiom_stmt {% id %} | provable_stmt {% id %}

      # Axiomatic assertion.
      axiom_stmt -> LABEL __ %a __ typecode (__ MATH_SYMBOL):* __ %dot {% ([l, ws1, a, ws2, t, list, ws4, d]) => 
        [l, a.text, t.text, list.map(([ws, v]) => v.text), d.text] 
      %}

      # Provable assertion.
      provable_stmt -> LABEL __ %p __ typecode (__ MATH_SYMBOL):* __ %proof __ proof __ %dot {%
        ([l, ws1, p, ws2, t, list, ws3, eq, ws4, proof, ws5, d]) => 
        [l, p.text, t.text, list.map(([ws, v]) => v.text), eq.text, proof, d.text]
      %}

      # A proof. Proofs may be interspersed by comments.
      # If ’?’ is in a proof it’s an "incomplete" proof.
      proof -> uncompressed_proof {% id %} | compressed_proof {% id %}

      uncompressed_proof -> (LABEL | "?") (__ (LABEL | "?")):* {% ([l, list]) => 
        l.concat(list.map(([ws, [v]]) => v)) 
      %}

      compressed_proof -> "("  (__ LABEL):* __ ")" __ COMPRESSED_PROOF_BLOCK
      {% 
        ([p1, labels, ws1, p2, ws2, proof]) => 
         [p1.text, labels.map(([ws, l]) => l), p2.text, proof] 
      %}

      typecode -> constant {% id %}
      filename -> MATH_SYMBOL {% id %}
      constant -> MATH_SYMBOL {% id %}
      variable -> MATH_SYMBOL {% id %}

      MATH_SYMBOL -> %sequence {% id %}

      # lexicon

      LABEL -> ( _LETTER_OR_DIGIT | "." | "-" | "_" ):+ {% ([str]) => str.join("") %}

      _LETTER_OR_DIGIT -> %sequence {% ([a], loc, r) => { return a.text.match(/[A-Za-z0-9]/) ? a : r } %}

      COMPRESSED_PROOF_BLOCK -> ([A-Z] | "?" | %ws):+ {% ([a]) => a.join("") %}

      # Define whitespace between tokens.
      WHITESPACE -> (%ws | %comment)

      # Whitespace: _ is optional, __ is mandatory.
      _  -> WHITESPACE:* {% (d) => null %}
      __ -> WHITESPACE:+ {% (d) => null %}
`);

function parse(code, handler = false) {
  const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar(handler)));
  parser.feed(code);
  return parser.results;
}

module.exports = {
  parse: parse,
  grammar: grammar,
};

},{"./lexer.js":8,"nearley":5,"nearley/lib/compile":2,"nearley/lib/generate":3,"nearley/lib/nearley-language-bootstrapped":4}],12:[function(require,module,exports){

},{}],13:[function(require,module,exports){
(function (process){(function (){
// 'path' module extracted from Node.js v8.11.1 (only the posix part)
// transplited with Babel

// Copyright Joyent, Inc. and other Node contributors.
//
// Permission is hereby granted, free of charge, to any person obtaining a
// copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to permit
// persons to whom the Software is furnished to do so, subject to the
// following conditions:
//
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
// OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN
// NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
// OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE
// USE OR OTHER DEALINGS IN THE SOFTWARE.

'use strict';

function assertPath(path) {
  if (typeof path !== 'string') {
    throw new TypeError('Path must be a string. Received ' + JSON.stringify(path));
  }
}

// Resolves . and .. elements in a path with directory names
function normalizeStringPosix(path, allowAboveRoot) {
  var res = '';
  var lastSegmentLength = 0;
  var lastSlash = -1;
  var dots = 0;
  var code;
  for (var i = 0; i <= path.length; ++i) {
    if (i < path.length)
      code = path.charCodeAt(i);
    else if (code === 47 /*/*/)
      break;
    else
      code = 47 /*/*/;
    if (code === 47 /*/*/) {
      if (lastSlash === i - 1 || dots === 1) {
        // NOOP
      } else if (lastSlash !== i - 1 && dots === 2) {
        if (res.length < 2 || lastSegmentLength !== 2 || res.charCodeAt(res.length - 1) !== 46 /*.*/ || res.charCodeAt(res.length - 2) !== 46 /*.*/) {
          if (res.length > 2) {
            var lastSlashIndex = res.lastIndexOf('/');
            if (lastSlashIndex !== res.length - 1) {
              if (lastSlashIndex === -1) {
                res = '';
                lastSegmentLength = 0;
              } else {
                res = res.slice(0, lastSlashIndex);
                lastSegmentLength = res.length - 1 - res.lastIndexOf('/');
              }
              lastSlash = i;
              dots = 0;
              continue;
            }
          } else if (res.length === 2 || res.length === 1) {
            res = '';
            lastSegmentLength = 0;
            lastSlash = i;
            dots = 0;
            continue;
          }
        }
        if (allowAboveRoot) {
          if (res.length > 0)
            res += '/..';
          else
            res = '..';
          lastSegmentLength = 2;
        }
      } else {
        if (res.length > 0)
          res += '/' + path.slice(lastSlash + 1, i);
        else
          res = path.slice(lastSlash + 1, i);
        lastSegmentLength = i - lastSlash - 1;
      }
      lastSlash = i;
      dots = 0;
    } else if (code === 46 /*.*/ && dots !== -1) {
      ++dots;
    } else {
      dots = -1;
    }
  }
  return res;
}

function _format(sep, pathObject) {
  var dir = pathObject.dir || pathObject.root;
  var base = pathObject.base || (pathObject.name || '') + (pathObject.ext || '');
  if (!dir) {
    return base;
  }
  if (dir === pathObject.root) {
    return dir + base;
  }
  return dir + sep + base;
}

var posix = {
  // path.resolve([from ...], to)
  resolve: function resolve() {
    var resolvedPath = '';
    var resolvedAbsolute = false;
    var cwd;

    for (var i = arguments.length - 1; i >= -1 && !resolvedAbsolute; i--) {
      var path;
      if (i >= 0)
        path = arguments[i];
      else {
        if (cwd === undefined)
          cwd = process.cwd();
        path = cwd;
      }

      assertPath(path);

      // Skip empty entries
      if (path.length === 0) {
        continue;
      }

      resolvedPath = path + '/' + resolvedPath;
      resolvedAbsolute = path.charCodeAt(0) === 47 /*/*/;
    }

    // At this point the path should be resolved to a full absolute path, but
    // handle relative paths to be safe (might happen when process.cwd() fails)

    // Normalize the path
    resolvedPath = normalizeStringPosix(resolvedPath, !resolvedAbsolute);

    if (resolvedAbsolute) {
      if (resolvedPath.length > 0)
        return '/' + resolvedPath;
      else
        return '/';
    } else if (resolvedPath.length > 0) {
      return resolvedPath;
    } else {
      return '.';
    }
  },

  normalize: function normalize(path) {
    assertPath(path);

    if (path.length === 0) return '.';

    var isAbsolute = path.charCodeAt(0) === 47 /*/*/;
    var trailingSeparator = path.charCodeAt(path.length - 1) === 47 /*/*/;

    // Normalize the path
    path = normalizeStringPosix(path, !isAbsolute);

    if (path.length === 0 && !isAbsolute) path = '.';
    if (path.length > 0 && trailingSeparator) path += '/';

    if (isAbsolute) return '/' + path;
    return path;
  },

  isAbsolute: function isAbsolute(path) {
    assertPath(path);
    return path.length > 0 && path.charCodeAt(0) === 47 /*/*/;
  },

  join: function join() {
    if (arguments.length === 0)
      return '.';
    var joined;
    for (var i = 0; i < arguments.length; ++i) {
      var arg = arguments[i];
      assertPath(arg);
      if (arg.length > 0) {
        if (joined === undefined)
          joined = arg;
        else
          joined += '/' + arg;
      }
    }
    if (joined === undefined)
      return '.';
    return posix.normalize(joined);
  },

  relative: function relative(from, to) {
    assertPath(from);
    assertPath(to);

    if (from === to) return '';

    from = posix.resolve(from);
    to = posix.resolve(to);

    if (from === to) return '';

    // Trim any leading backslashes
    var fromStart = 1;
    for (; fromStart < from.length; ++fromStart) {
      if (from.charCodeAt(fromStart) !== 47 /*/*/)
        break;
    }
    var fromEnd = from.length;
    var fromLen = fromEnd - fromStart;

    // Trim any leading backslashes
    var toStart = 1;
    for (; toStart < to.length; ++toStart) {
      if (to.charCodeAt(toStart) !== 47 /*/*/)
        break;
    }
    var toEnd = to.length;
    var toLen = toEnd - toStart;

    // Compare paths to find the longest common path from root
    var length = fromLen < toLen ? fromLen : toLen;
    var lastCommonSep = -1;
    var i = 0;
    for (; i <= length; ++i) {
      if (i === length) {
        if (toLen > length) {
          if (to.charCodeAt(toStart + i) === 47 /*/*/) {
            // We get here if `from` is the exact base path for `to`.
            // For example: from='/foo/bar'; to='/foo/bar/baz'
            return to.slice(toStart + i + 1);
          } else if (i === 0) {
            // We get here if `from` is the root
            // For example: from='/'; to='/foo'
            return to.slice(toStart + i);
          }
        } else if (fromLen > length) {
          if (from.charCodeAt(fromStart + i) === 47 /*/*/) {
            // We get here if `to` is the exact base path for `from`.
            // For example: from='/foo/bar/baz'; to='/foo/bar'
            lastCommonSep = i;
          } else if (i === 0) {
            // We get here if `to` is the root.
            // For example: from='/foo'; to='/'
            lastCommonSep = 0;
          }
        }
        break;
      }
      var fromCode = from.charCodeAt(fromStart + i);
      var toCode = to.charCodeAt(toStart + i);
      if (fromCode !== toCode)
        break;
      else if (fromCode === 47 /*/*/)
        lastCommonSep = i;
    }

    var out = '';
    // Generate the relative path based on the path difference between `to`
    // and `from`
    for (i = fromStart + lastCommonSep + 1; i <= fromEnd; ++i) {
      if (i === fromEnd || from.charCodeAt(i) === 47 /*/*/) {
        if (out.length === 0)
          out += '..';
        else
          out += '/..';
      }
    }

    // Lastly, append the rest of the destination (`to`) path that comes after
    // the common path parts
    if (out.length > 0)
      return out + to.slice(toStart + lastCommonSep);
    else {
      toStart += lastCommonSep;
      if (to.charCodeAt(toStart) === 47 /*/*/)
        ++toStart;
      return to.slice(toStart);
    }
  },

  _makeLong: function _makeLong(path) {
    return path;
  },

  dirname: function dirname(path) {
    assertPath(path);
    if (path.length === 0) return '.';
    var code = path.charCodeAt(0);
    var hasRoot = code === 47 /*/*/;
    var end = -1;
    var matchedSlash = true;
    for (var i = path.length - 1; i >= 1; --i) {
      code = path.charCodeAt(i);
      if (code === 47 /*/*/) {
          if (!matchedSlash) {
            end = i;
            break;
          }
        } else {
        // We saw the first non-path separator
        matchedSlash = false;
      }
    }

    if (end === -1) return hasRoot ? '/' : '.';
    if (hasRoot && end === 1) return '//';
    return path.slice(0, end);
  },

  basename: function basename(path, ext) {
    if (ext !== undefined && typeof ext !== 'string') throw new TypeError('"ext" argument must be a string');
    assertPath(path);

    var start = 0;
    var end = -1;
    var matchedSlash = true;
    var i;

    if (ext !== undefined && ext.length > 0 && ext.length <= path.length) {
      if (ext.length === path.length && ext === path) return '';
      var extIdx = ext.length - 1;
      var firstNonSlashEnd = -1;
      for (i = path.length - 1; i >= 0; --i) {
        var code = path.charCodeAt(i);
        if (code === 47 /*/*/) {
            // If we reached a path separator that was not part of a set of path
            // separators at the end of the string, stop now
            if (!matchedSlash) {
              start = i + 1;
              break;
            }
          } else {
          if (firstNonSlashEnd === -1) {
            // We saw the first non-path separator, remember this index in case
            // we need it if the extension ends up not matching
            matchedSlash = false;
            firstNonSlashEnd = i + 1;
          }
          if (extIdx >= 0) {
            // Try to match the explicit extension
            if (code === ext.charCodeAt(extIdx)) {
              if (--extIdx === -1) {
                // We matched the extension, so mark this as the end of our path
                // component
                end = i;
              }
            } else {
              // Extension does not match, so our result is the entire path
              // component
              extIdx = -1;
              end = firstNonSlashEnd;
            }
          }
        }
      }

      if (start === end) end = firstNonSlashEnd;else if (end === -1) end = path.length;
      return path.slice(start, end);
    } else {
      for (i = path.length - 1; i >= 0; --i) {
        if (path.charCodeAt(i) === 47 /*/*/) {
            // If we reached a path separator that was not part of a set of path
            // separators at the end of the string, stop now
            if (!matchedSlash) {
              start = i + 1;
              break;
            }
          } else if (end === -1) {
          // We saw the first non-path separator, mark this as the end of our
          // path component
          matchedSlash = false;
          end = i + 1;
        }
      }

      if (end === -1) return '';
      return path.slice(start, end);
    }
  },

  extname: function extname(path) {
    assertPath(path);
    var startDot = -1;
    var startPart = 0;
    var end = -1;
    var matchedSlash = true;
    // Track the state of characters (if any) we see before our first dot and
    // after any path separator we find
    var preDotState = 0;
    for (var i = path.length - 1; i >= 0; --i) {
      var code = path.charCodeAt(i);
      if (code === 47 /*/*/) {
          // If we reached a path separator that was not part of a set of path
          // separators at the end of the string, stop now
          if (!matchedSlash) {
            startPart = i + 1;
            break;
          }
          continue;
        }
      if (end === -1) {
        // We saw the first non-path separator, mark this as the end of our
        // extension
        matchedSlash = false;
        end = i + 1;
      }
      if (code === 46 /*.*/) {
          // If this is our first dot, mark it as the start of our extension
          if (startDot === -1)
            startDot = i;
          else if (preDotState !== 1)
            preDotState = 1;
      } else if (startDot !== -1) {
        // We saw a non-dot and non-path separator before our dot, so we should
        // have a good chance at having a non-empty extension
        preDotState = -1;
      }
    }

    if (startDot === -1 || end === -1 ||
        // We saw a non-dot character immediately before the dot
        preDotState === 0 ||
        // The (right-most) trimmed path component is exactly '..'
        preDotState === 1 && startDot === end - 1 && startDot === startPart + 1) {
      return '';
    }
    return path.slice(startDot, end);
  },

  format: function format(pathObject) {
    if (pathObject === null || typeof pathObject !== 'object') {
      throw new TypeError('The "pathObject" argument must be of type Object. Received type ' + typeof pathObject);
    }
    return _format('/', pathObject);
  },

  parse: function parse(path) {
    assertPath(path);

    var ret = { root: '', dir: '', base: '', ext: '', name: '' };
    if (path.length === 0) return ret;
    var code = path.charCodeAt(0);
    var isAbsolute = code === 47 /*/*/;
    var start;
    if (isAbsolute) {
      ret.root = '/';
      start = 1;
    } else {
      start = 0;
    }
    var startDot = -1;
    var startPart = 0;
    var end = -1;
    var matchedSlash = true;
    var i = path.length - 1;

    // Track the state of characters (if any) we see before our first dot and
    // after any path separator we find
    var preDotState = 0;

    // Get non-dir info
    for (; i >= start; --i) {
      code = path.charCodeAt(i);
      if (code === 47 /*/*/) {
          // If we reached a path separator that was not part of a set of path
          // separators at the end of the string, stop now
          if (!matchedSlash) {
            startPart = i + 1;
            break;
          }
          continue;
        }
      if (end === -1) {
        // We saw the first non-path separator, mark this as the end of our
        // extension
        matchedSlash = false;
        end = i + 1;
      }
      if (code === 46 /*.*/) {
          // If this is our first dot, mark it as the start of our extension
          if (startDot === -1) startDot = i;else if (preDotState !== 1) preDotState = 1;
        } else if (startDot !== -1) {
        // We saw a non-dot and non-path separator before our dot, so we should
        // have a good chance at having a non-empty extension
        preDotState = -1;
      }
    }

    if (startDot === -1 || end === -1 ||
    // We saw a non-dot character immediately before the dot
    preDotState === 0 ||
    // The (right-most) trimmed path component is exactly '..'
    preDotState === 1 && startDot === end - 1 && startDot === startPart + 1) {
      if (end !== -1) {
        if (startPart === 0 && isAbsolute) ret.base = ret.name = path.slice(1, end);else ret.base = ret.name = path.slice(startPart, end);
      }
    } else {
      if (startPart === 0 && isAbsolute) {
        ret.name = path.slice(1, startDot);
        ret.base = path.slice(1, end);
      } else {
        ret.name = path.slice(startPart, startDot);
        ret.base = path.slice(startPart, end);
      }
      ret.ext = path.slice(startDot, end);
    }

    if (startPart > 0) ret.dir = path.slice(0, startPart - 1);else if (isAbsolute) ret.dir = '/';

    return ret;
  },

  sep: '/',
  delimiter: ':',
  win32: null,
  posix: null
};

posix.posix = posix;

module.exports = posix;

}).call(this)}).call(this,require('_process'))
},{"_process":14}],14:[function(require,module,exports){
// shim for using process in browser
var process = module.exports = {};

// cached from whatever global is present so that test runners that stub it
// don't break things.  But we need to wrap it in a try catch in case it is
// wrapped in strict mode code which doesn't define any globals.  It's inside a
// function because try/catches deoptimize in certain engines.

var cachedSetTimeout;
var cachedClearTimeout;

function defaultSetTimout() {
    throw new Error('setTimeout has not been defined');
}
function defaultClearTimeout () {
    throw new Error('clearTimeout has not been defined');
}
(function () {
    try {
        if (typeof setTimeout === 'function') {
            cachedSetTimeout = setTimeout;
        } else {
            cachedSetTimeout = defaultSetTimout;
        }
    } catch (e) {
        cachedSetTimeout = defaultSetTimout;
    }
    try {
        if (typeof clearTimeout === 'function') {
            cachedClearTimeout = clearTimeout;
        } else {
            cachedClearTimeout = defaultClearTimeout;
        }
    } catch (e) {
        cachedClearTimeout = defaultClearTimeout;
    }
} ())
function runTimeout(fun) {
    if (cachedSetTimeout === setTimeout) {
        //normal enviroments in sane situations
        return setTimeout(fun, 0);
    }
    // if setTimeout wasn't available but was latter defined
    if ((cachedSetTimeout === defaultSetTimout || !cachedSetTimeout) && setTimeout) {
        cachedSetTimeout = setTimeout;
        return setTimeout(fun, 0);
    }
    try {
        // when when somebody has screwed with setTimeout but no I.E. maddness
        return cachedSetTimeout(fun, 0);
    } catch(e){
        try {
            // When we are in I.E. but the script has been evaled so I.E. doesn't trust the global object when called normally
            return cachedSetTimeout.call(null, fun, 0);
        } catch(e){
            // same as above but when it's a version of I.E. that must have the global object for 'this', hopfully our context correct otherwise it will throw a global error
            return cachedSetTimeout.call(this, fun, 0);
        }
    }


}
function runClearTimeout(marker) {
    if (cachedClearTimeout === clearTimeout) {
        //normal enviroments in sane situations
        return clearTimeout(marker);
    }
    // if clearTimeout wasn't available but was latter defined
    if ((cachedClearTimeout === defaultClearTimeout || !cachedClearTimeout) && clearTimeout) {
        cachedClearTimeout = clearTimeout;
        return clearTimeout(marker);
    }
    try {
        // when when somebody has screwed with setTimeout but no I.E. maddness
        return cachedClearTimeout(marker);
    } catch (e){
        try {
            // When we are in I.E. but the script has been evaled so I.E. doesn't  trust the global object when called normally
            return cachedClearTimeout.call(null, marker);
        } catch (e){
            // same as above but when it's a version of I.E. that must have the global object for 'this', hopfully our context correct otherwise it will throw a global error.
            // Some versions of I.E. have different rules for clearTimeout vs setTimeout
            return cachedClearTimeout.call(this, marker);
        }
    }



}
var queue = [];
var draining = false;
var currentQueue;
var queueIndex = -1;

function cleanUpNextTick() {
    if (!draining || !currentQueue) {
        return;
    }
    draining = false;
    if (currentQueue.length) {
        queue = currentQueue.concat(queue);
    } else {
        queueIndex = -1;
    }
    if (queue.length) {
        drainQueue();
    }
}

function drainQueue() {
    if (draining) {
        return;
    }
    var timeout = runTimeout(cleanUpNextTick);
    draining = true;

    var len = queue.length;
    while(len) {
        currentQueue = queue;
        queue = [];
        while (++queueIndex < len) {
            if (currentQueue) {
                currentQueue[queueIndex].run();
            }
        }
        queueIndex = -1;
        len = queue.length;
    }
    currentQueue = null;
    draining = false;
    runClearTimeout(timeout);
}

process.nextTick = function (fun) {
    var args = new Array(arguments.length - 1);
    if (arguments.length > 1) {
        for (var i = 1; i < arguments.length; i++) {
            args[i - 1] = arguments[i];
        }
    }
    queue.push(new Item(fun, args));
    if (queue.length === 1 && !draining) {
        runTimeout(drainQueue);
    }
};

// v8 likes predictible objects
function Item(fun, array) {
    this.fun = fun;
    this.array = array;
}
Item.prototype.run = function () {
    this.fun.apply(null, this.array);
};
process.title = 'browser';
process.browser = true;
process.env = {};
process.argv = [];
process.version = ''; // empty string to avoid regexp issues
process.versions = {};

function noop() {}

process.on = noop;
process.addListener = noop;
process.once = noop;
process.off = noop;
process.removeListener = noop;
process.removeAllListeners = noop;
process.emit = noop;
process.prependListener = noop;
process.prependOnceListener = noop;

process.listeners = function (name) { return [] }

process.binding = function (name) {
    throw new Error('process.binding is not supported');
};

process.cwd = function () { return '/' };
process.chdir = function (dir) {
    throw new Error('process.chdir is not supported');
};
process.umask = function() { return 0; };

},{}]},{},[10])(10)
});
