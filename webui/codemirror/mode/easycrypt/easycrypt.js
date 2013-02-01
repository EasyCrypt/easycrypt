CodeMirror.defineMode("easycrypt", function(config, parserConfig) {
  return {
    token: function(stream, state) {
      stream.next();
      return null;
    }
  }
});

CodeMirror.defineMIME("text/x-easycrypt", "easycrypt");
