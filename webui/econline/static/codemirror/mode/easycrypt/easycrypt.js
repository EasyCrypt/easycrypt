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
    //var newLine = '\\n';

    if (hooks[ch]) {
      var result = hooks[ch](stream, state);
      if (result !== false) return result;
    }
    
    //if (ch == '\\') {
    //	var match = stream.match(new RegExp(newLine.charAt(1)));
   // 	alert(match);
    //}
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
            if (cur == 'op') {
            	tokenOperatorName(stream, state);	
            }
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

  function tokenOperatorName(stream, state) {
  	stream.eatSpace();
  	var lenghtOpAndSpaces = stream.current().length;
    stream.eatWhile(/\w/);
    var lengthOpAndName = stream.current().length;
    var operatorName =  stream.current().substring(lengthOpAndName-lenghtOpAndSpaces-1, lengthOpAndName);
    
    state.operatorsList[state.operatorsCounter] = new Operator(operatorName, state.lines);
    state.operatorsCounter = state.operatorsCounter + 1;
	
    stream.backUp(lengthOpAndName-lenghtOpAndSpaces);
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

  function Operator(name, line) {
  	this.name = name;
  	this.line = line;
  }

  return {
    startState: function(basecolumn) {
      return {
        tokenize: null,
        context: new Context((basecolumn || 0) - indentUnit, 0, "top", false),
        indented: 0,
        startOfLine: true,
        operatorsList: new Array(),
        operatorsCounter : 0,
        lines: 1
      };
    },

    token: function(stream, state) {
      var ctx = state.context;
      if (stream.sol()) {
        if (ctx.align == null) ctx.align = false;
        state.indented = stream.indentation();
        state.startOfLine = true;
        // counting number of lines
        state.lines = state.lines + 1;
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

  // Generated on Sun Oct 13 21:54:15 2013
  var cKeywords = "Pr admit alias apply as assert assumption axiom bd_eq bd_hoare bdhoare_deno beta by bypr call case cfold change checkproof claim class clear clone compute congr conseq const cut datatype debug declare delta do drop eager elim elimT else end eqobs_in equiv equiv_deno exfalso exists export fel fieldeq first fission forall fun fusion generalize glob hoare idtac if import in inline instance intros iota islossless kill lambda last left lemma let local logic modpath module nosmt of off on op pose pr_bounded pr_false pragma pred print progress proof prover qed rcondf rcondt realize reflexivity require res return rewrite right ringeq rnd same save section self seq simplify skip smt sp split splitwhile strict subst swap symmetry then theory timeout transitivity trivial try type undo unroll using var while why3 with wp zeta"
  // END

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