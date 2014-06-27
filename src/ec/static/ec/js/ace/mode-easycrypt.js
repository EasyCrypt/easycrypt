define('ace/mode/easycrypt',
      ['require', 'exports', 'module' , 'ace/lib/oop', 'ace/mode/text',
       'ace/mode/easycrypt_highlight_rules', 'ace/mode/matching_brace_outdent', 'ace/range'],
       function(require, exports, module) {

var oop = require("../lib/oop");
var TextMode = require("./text").Mode;
var EasycryptHighlightRules = require("./easycrypt_highlight_rules").EasycryptHighlightRules;
var MatchingBraceOutdent = require("./matching_brace_outdent").MatchingBraceOutdent;
var Range = require("../range").Range;

var Mode = function() {
  this.HighlightRules = EasycryptHighlightRules;
  this.$outdent = new MatchingBraceOutdent();
  // this.foldingRules = new EasyCryptFoldMode();
};
oop.inherits(Mode, TextMode);

var indenter = /(?:[({[=:,-]|(?:lemma|equiv|hoare|realize|proof.))\s*$/;

(function() {
  this.toggleCommentLines = function(state, doc, startRow, endRow) {
    var i, line;
    var outdent = true;
    var re = /^\s*\(\*(.*)\*\)/;

    for (i = startRow; i <= endRow; i++) {
      if (!re.test(doc.getLine(i))) {
        outdent = false;
        break;
      }
    }

    var range = new Range(0, 0, 0, 0);
    for (i = startRow; i <= endRow; i++) {
      line = doc.getLine(i);
      range.start.row = i;
      range.end.row = i;
      range.end.column = line.length;

      doc.replace(range, outdent ? line.match(re)[1] : "(*" + line + "*)");
    }
  };

  this.getNextLineIndent = function(state, line, tab) {
    var indent = this.$getIndent(line);
    var tokens = this.getTokenizer().getLineTokens(line, state).tokens;

    if (!(tokens.length && tokens[tokens.length - 1].type === 'comment')
        && state === 'start' && indenter.test(line))
      indent += tab;

    return indent;
  };

  this.checkOutdent = function(state, line, input) {
    return this.$outdent.checkOutdent(line, input);
  };

  this.autoOutdent = function(state, doc, row) {
    this.$outdent.autoOutdent(doc, row);
  };

  this.$id = "ace/mode/easycrypt";
      }).call(Mode.prototype);

      exports.Mode = Mode;
    });

define('ace/mode/easycrypt_highlight_rules',
      ['require', 'exports', 'module', 'ace/lib/oop', 'ace/mode/text_highlight_rules'],
      function(require, exports, module) {

var oop = require("../lib/oop");
var TextHighlightRules = require("./text_highlight_rules").TextHighlightRules;

var EasycryptHighlightRules = function() {
  /* Keywords, from "scripts/keywords.py" */
  /* -------------------------------------------------------------- */
  var bytac = "assumption|by|reflexivity|smt";
  var dangerous = "admit";
  var global = ("Pr|Top|as|axiom|checkproof|claim|class|clone|const|datatype|declare|end|export|"
      + "import|instance|lemma|local|module|nolocals|nosmt|of|off|on|op|pred|print|proof|"
      + "prover|qed|realize|record|require|save|section|theory|timeout|type|why3|with")
  var internal = "debug|pragma|undo";
  var prog = ("assert|bd_hoare|else|equiv|exists|forall|fun|glob|hoare|if|in|islossless|lambda|"
      + "let|res|return|then|var|while");
  var tactic = ("alias|apply|bd_eq|bdhoare_deno|beta|bypr|call|case|cfold|change|clear|compute|"
      + "congr|conseq|cut|delta|eager|elim|elimT|eqobs_in|equiv_deno|exfalso|fel|fieldeq|"
      + "fission|fusion|generalize|idtac|inline|intros|iota|kill|left|logic|modpath|pose|"
      + "pr_bounded|pr_false|progress|rcondf|rcondt|rewrite|right|ringeq|rnd|same|seq|"
      + "simplify|skip|sp|split|splitwhile|subst|swap|symmetry|transitivity|trivial|"
      + "unroll|using|wp|zeta")
  var tactical = ("do|expect|first|last|strict|try");
  /* -------------------------------------------------------------- */

  var types = "int|nat|bool|char|distr";
  var builtinConstants = "true|false";

  var builtinFunctions = ("mu");

  var keywordMapper = this.createKeywordMapper({
    "keyword" : global + "|" + prog,
    "keyword.operator" : tactic + "|" + tactical + "|" + bytac,
    "constant.language" : builtinConstants,
    "support.function" : builtinFunctions,
    "support.type" : types,
    "invalid" : internal,
    "invalid.deprecated" : dangerous,
    "variable.language" : "this",
  }, "identifier");

  var integer = "(?:(?:[1-9]\\d*)|(?:0))";

  this.$rules = {
    "start" : [
        {
          token : "comment", // self-contained comment
          regex : '\\(\\*.*?\\*\\)\\s*?$'
        },
        {
          token : "comment", // opening multiline comment
          regex : '\\(\\*.*',
          next : "comment"
        },
        {
          token : "string", // single line
          regex : '["](?:(?:\\\\.)|(?:[^"\\\\]))*?["]'
        },
        {
          token : "string", // " string
          regex : '"',
          next : "qstring"
        },
        {
          token : "support.constant", // type variables + memory locations
          regex : "(?:'(?:[a-z][a-zA-Z0-9_']*|_[a-zA-Z0-9_']+)|" +
                     "&(?:[a-z][a-zA-Z0-9_']*|_[a-zA-Z0-9_']+|[0-9]+))\\b"
        },
        {
          token : keywordMapper, // idents + keywords
          regex : "(?:[a-zA-Z][a-zA-Z0-9_']*|_[a-zA-Z0-9_']+)\\b"
        },
        {
          token : "constant.numeric", // integer
          regex : integer + "\\b"
        },
        {
          token : "keyword.operator", // operators
          regex : "\\+\\.|\\-\\.|\\*\\.|\\/\\.|#|;;|\\+|\\-|\\*|\\*\\*\\/|\\/\\/|%|<<|>>|&|\\||\\^|~|<|>|<=|=>|==|!=|<>|<-|="
        }, {
          token : "paren.lparen", // left parens
          regex : "[[({]"
        }, {
          token : "paren.rparen", // right parens
          regex : "[\\])}]"
        }, {
          token : "text", // anything else
          regex : "\\s+"
        } ],
    "comment" : [ {
      token : "comment", // closing comment
      regex : ".*?\\*\\)",
      next : "start"
    }, {
      token : "comment", // comment spanning whole line
      regex : ".+"
    } ],

    "qstring" : [ {
      token : "string",
      regex : '"',
      next : "start"
    }, {
      token : "string",
      regex : '.+'
    } ]
  };
};

oop.inherits(EasycryptHighlightRules, TextHighlightRules);
exports.EasycryptHighlightRules = EasycryptHighlightRules;
});

/* -------------------------------------------------------------- */
define('ace/mode/matching_brace_outdent', [ 'require', 'exports', 'module', 'ace/range' ], function(require, exports, module) {
var Range = require("../range").Range;

var MatchingBraceOutdent = function() {};

(function() {
  this.checkOutdent = function(line, input) {
    return /[}\.]/.test(input);
  };
  this.autoOutdent = function(doc, row) {
    var line = doc.getLine(row);

    var match = line.match(/^(\s+)(?:qed|proof|save)\./)
    if (match) {
      doc.replace(new Range(row, 0, row, match[1].length), "");
    } else {
      match = line.match(/^(\s*\})/);

      if (!match) return 0;

      var column = match[1].length;
      var openBracePos = doc.findMatchingBracket({row: row, column: column});

      if (!openBracePos || openBracePos.row == row) return 0;

      var indent = this.$getIndent(doc.getLine(openBracePos.row));
      doc.replace(new Range(row, 0, row, column-1), indent);
    }
  };
  this.$getIndent = function(line) {
    return line.match(/^\s*/)[0];
  };
}).call(MatchingBraceOutdent.prototype);

exports.MatchingBraceOutdent = MatchingBraceOutdent;
});
