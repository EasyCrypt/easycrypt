CodeMirror.defineMode("easycrypt", function(config, parserConfig) {
  var indentUnit = config.indentUnit,
      statementIndentUnit = parserConfig.statementIndentUnit || indentUnit,
      dontAlignCalls = parserConfig.dontAlignCalls,
      keywords = parserConfig.keywords || {},
      builtin = parserConfig.builtin || {},
      blockKeywords = parserConfig.blockKeywords || {},
      atoms = parserConfig.atoms || {},
      hooks = parserConfig.hooks || {},
      multiLineStrings = parserConfig.multiLineStrings;
  var isOperatorChar = /[+\-*&%=<>!?|\/]/;
  var ident  = "(?:[a-zA-Z][a-zA-Z0-9_']*|_[a-zA-Z0-9_']+)";
  var qident = $.format('(?:{0}\\.)*(?:{0})', ident);
  var curPunc;

  function tokenBase(stream, state) {
    var ch = stream.next();
    if (hooks[ch]) {
      var result = hooks[ch](stream, state);
      if (result !== false) return result;
    }
    if (ch == '"') {
      state.tokenize = tokenString(ch);
      return state.tokenize(stream, state);
    }
    if (/[\[\]{},;\:\.]/.test(ch)) {
      curPunc = ch;
      return "punctuation";
    }
    if (/\d/.test(ch)) {
      stream.eatWhile(/\d/);
      return "number";
    }
    if (ch == "(") {
      if (stream.eat("*")) {
        state.tokenize = tokenComment;
        return tokenComment(stream, state);
      }
    }
    if (isOperatorChar.test(ch)) {
      stream.eatWhile(isOperatorChar);
      return "operator";
    }

    if (ch == '_')
    	return "anontype";

    if (/\w/.test(ch)) {
    	stream.eatWhile(/\w/);    	
        var cur = stream.current();
        if (keywords.propertyIsEnumerable(cur)) {
            if (blockKeywords.propertyIsEnumerable(cur)) curPunc = "newstatement";
            return "keyword";
       }
       if (builtin.propertyIsEnumerable(cur)) {
    	   if (blockKeywords.propertyIsEnumerable(cur)) curPunc = "newstatement";
           return "builtin";
       }
       if (atoms.propertyIsEnumerable(cur)) return "atom";
    }

    stream.backUp(stream.current().length);

    if (stream.match(RegExp("^" + qident)))
    	return "variable";

    stream.next();
    return "unknown";
  }

  function tokenString(quote) {
    return function(stream, state) {
      var escaped = false, next, end = false;
      while ((next = stream.next()) != null) {
        if (next == quote && !escaped) {end = true; break;}
        escaped = !escaped && next == "\\";
      }
      if (end || !(escaped || multiLineStrings))
        state.tokenize = null;
      return "string";
    };
  }

  function tokenComment(stream, state) {
    var maybeEnd = false, ch;
    while (ch = stream.next()) {
	if (ch == ")" && maybeEnd && stream.eol()) {
        state.tokenize = null;
        break;
      }
      maybeEnd = (ch == "*");
    }
    return "comment";
  }

  function Context(indented, column, type, align, prev) {
    this.indented = indented;
    this.column = column;
    this.type = type;
    this.align = align;
    this.prev = prev;
  }
  function pushContext(state, col, type) {
    var indent = state.indented;
    if (state.context && state.context.type == "statement")
      indent = state.context.indented;
    return state.context = new Context(indent, col, type, null, state.context);
  }
  function popContext(state) {
    var t = state.context.type;
    if (t == ")" || t == "]" || t == "}")
      state.indented = state.context.indented;
    return state.context = state.context.prev;
  }

  // Interface

  return {
    startState: function(basecolumn) {
      return {
        tokenize: null,
        context: new Context((basecolumn || 0) - indentUnit, 0, "top", false),
        indented: 0,
        startOfLine: true
      };
    },

    token: function(stream, state) {
      var ctx = state.context;
      if (stream.sol()) {
        if (ctx.align == null) ctx.align = false;
        state.indented = stream.indentation();
        state.startOfLine = true;
      }
      if (stream.eatSpace()) return null;
      curPunc = null;
      var style = (state.tokenize || tokenBase)(stream, state);
      if (style == "comment" || style == "meta") return style;
      if (ctx.align == null) ctx.align = true;

      if ((curPunc == ";" || curPunc == ":" || curPunc == "," || curPunc == ".") && ctx.type == "statement") popContext(state);
      else if (curPunc == "{") pushContext(state, stream.column(), "}");
      else if (curPunc == "[") pushContext(state, stream.column(), "]");
      else if (curPunc == "(") pushContext(state, stream.column(), ")");
      else if (curPunc == "}") {
        while (ctx.type == "statement") ctx = popContext(state);
        if (ctx.type == "}") ctx = popContext(state);
        while (ctx.type == "statement") ctx = popContext(state);
      }
      else if (curPunc == ctx.type) popContext(state);
      else if (((ctx.type == "}" || ctx.type == "top") && curPunc != ';') || (ctx.type == "statement" && curPunc == "newstatement"))
        pushContext(state, stream.column(), "statement");
      state.startOfLine = false;
      return style;
    },

    electricChars: "{}"
  };
});

(function() {
  function words(str) {
    var obj = {}, words = str.split(" ");
    for (var i = 0; i < words.length; ++i) obj[words[i]] = true;
    return obj;
  }
  var cKeywords = "forall exists let in var fun if then else while assert return using"
	  			+ " compute same idtac assumption intros split left right elim apply trivial"
	  			+ " admit axiom lemma proof save claim cnst drop end import export module"
	  			+ " op pred require theory type print why3 as Pr clone with prover checkproof timeout undo";        


/*  function cppHook(stream, state) {
    if (!state.startOfLine) return false;
    for (;;) {
      if (stream.skipTo("\\")) {
        stream.next();
        if (stream.eol()) {
          state.tokenize = cppHook;
          break;
        }
      } else {
        stream.skipToEnd();
        state.tokenize = null;
        break;
      }
    }
    return "meta";
  } */

CodeMirror.defineMIME("text/x-easycrypt", {
    name: "easycrypt",
    keywords: words(cKeywords),
    blockKeywords: words("if while forall"),
    atoms: words("null"),
    //hooks: {"#": cppHook}
  });

}());