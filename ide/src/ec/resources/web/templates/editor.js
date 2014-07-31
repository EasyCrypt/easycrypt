/* ------------------------------------------------------------------------ */
function create_editor(document) {
    editor = ace.edit("editor");
    editor.ecdoc = window.ecdoc;

    editor.setTheme("ace/theme/xcode");
    editor.setFontSize("14px");

    editor.getSession().setMode("ace/mode/easycrypt");
    editor.getSession().setValue("");

    editor.ecdoc.loaded.connect(function () {
    	this.setValue(this.ecdoc.contents);
    	this.gotoLine(0, 0, false);
    }.bind(editor));
    
    return editor;
}
