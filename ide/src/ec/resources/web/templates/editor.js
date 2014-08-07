/* ------------------------------------------------------------------------ */
function create_editor(manager) {
    editor = ace.edit("editor");
    editor.ecmanager = manager;
    editor.ecdoc = null;

    editor.setTheme("ace/theme/xcode");
    editor.setFontSize("14px");

    editor.getSession().setMode("ace/mode/easycrypt");
    editor.getSession().setValue("");

    editor.ecmanager.loaded.connect(function () {
    	this.ecdoc = manager.document;
    	console.log(this.ecdoc);
    }.bind(editor));
    
    return editor;
}
