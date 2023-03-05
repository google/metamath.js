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
