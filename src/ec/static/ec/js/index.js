/* ---------------------------------------------------------------- */
var Project = function(id, name) {
  this.id       = id;
  this.name     = name;
  this.files    = [];

  this.is_unfolded = false;
}

/* ---------------------------------------------------------------- */
var File = function(id, name, contents, project) {
  this.id       = id;
  this.name     = name;
  this.contents = contents;
  this.project  = project;

  this.session  = null;
}

/* ---------------------------------------------------------------- */
var Tab = function(id, session, file, display) {
  this.id      = id;
  this.session = session;
  this.file    = file || null;
  this.display = display || (file ? file.name : "<detached tab " + id + ">");

  this.ui      = null;  // jQuery object containing the tab (<li>) in the DOM
}

/* ---------------------------------------------------------------- */
var Workspace = function() {
  this.ui       = null;
  this.projects = [];
  this.tabs     = [];
  this.active   = null;

  this.editor   = null;

  this.ui = {}
  this.ui.treeview = $('#projects');
  this.ui.contents = $('#contents');
  this.ui.tabctl   = $('#tabs');

  this.load();
}


/* ---------------------------------------------------------------- */
Workspace.prototype.set_session_star_event = function(session) {
  session.on('change', function(session, e) {
    if (!session.changed) {
      session.changed = true;
      var idx = this.find_tab_by_session(session);
      if (idx != -1) {
        var ui_tab_a = this.tabs[idx].ui.children("a");
        ui_tab_a.text(ui_tab_a.text() + "*");
      }
    }
  }.bind(this, session));
}

/* ---------------------------------------------------------------- */
Workspace.prototype.get_file_contents = function(file) {
  $.get('files/' + file.id, (function (file,contents) {
    file.contents = contents;
    file.session.setValue(contents);
    file.session.changed = false;
    this.set_session_star_event(file.session);
    this.refresh_editor();
  }).bind(this,file));
}

Workspace.prototype.push_file_contents = function(file) {
  var tab = this.tabs[this.find_tab_by_file_id(file.id)];
  file.contents = tab.session.getValue();
  if (tab.session.changed) {
    $.post('files/' + file.id, {contents:file.contents}, function(resp) {
      if (resp == "OK") {
        var ui_tab_a = tab.ui.children("a");
        ui_tab_a.text(ui_tab_a.text().slice(0,-1));
        tab.session.changed = false;
      };
      this.set_session_star_event(tab.session);
    }.bind(this));
  };
}

/* ---------------------------------------------------------------- */
Workspace.prototype.refresh_projects = function() {
  this.ui.treeview.children().remove();
  for (var i = 0; i < this.projects.length; ++i) {
    var project = this.projects[i];

    var expand_proj = glyph(project.is_unfolded ? 'glyphicon-chevron-down' : 'glyphicon-chevron-up');
    var target_id = "proj_files_" + i;
    expand_proj.attr('data-toggle', 'collapse').attr('data-target', '#'+target_id);
    var files_col = col(11, 1).addClass('collapse').attr('id', target_id);
    if (project.is_unfolded) files_col.addClass('in');

    var toggle_glyph = this._callback_for_toggle_glyph(project, expand_proj);
    files_col.on('shown.bs.collapse', toggle_glyph);
    files_col.on('hidden.bs.collapse', toggle_glyph);

    for (var j = 0; j < project.files.length; ++j) {
      var file      = project.files[j];
      var filelink  = $('<a>').text(file.name).attr('href','#');
      filelink.on('click', this._callback_for_open_file_by_id(file.id));
      var rm_but = glyph('glyphicon-remove pull-right red');
      rm_but.on('click', this._callback_for_rm_file(file.id));
      files_col.append(row(filelink, rm_but));
    }
    var add_but = glyph('glyphicon-plus');
    add_but.on('click', this._callback_for_add_file_modal(project.id));
    files_col.append(row(add_but));

    var project_tree =
      row(col(12,0, row(expand_proj, " ", project.name),
                    row(files_col),
                    $('<hr />')));

    this.ui.treeview.append(project_tree);
  }
}

Workspace.prototype.refresh_editor = function() {
  if (this.active != null) {
    var current_file = this.active.file;
    if (!current_file.contents) {
      this.get_file_contents(current_file);
    }
    this.editor.setSession(this.active.file.session);
    this.editor.setReadOnly(!current_file.contents);
  } else {
    this.editor.setValue("");
    this.editor.setReadOnly(true);
  }
}

Workspace.prototype.refresh_ui = function() {
  this.refresh_projects();
  this.refresh_editor();
}

/* ---------------------------------------------------------------- */
Workspace.prototype.load_projects = function() {
  $.get('projects', function(ps) {
    var new_projects = [];
    for (var i = 0; i < ps.length; ++i) {
      var p = ps[i];
      var project = new Project(p.id, p.name);
      if (prev = this.find_project_by_id(p.id)) {
        project.is_unfolded = prev.is_unfolded;
      }
      for (var j = 0; j < p.files.length; ++j) {
        var file = p.files[j];
        project.files.push(new File(file.id, file.name, null, p));
      }
      new_projects.push(project);
    }
    this.projects = new_projects;

    this.refresh_projects();
  }.bind(this));
}

Workspace.prototype.load_editor = function() {
  this.editor = ace.edit("editor");
  this.editor.setTheme("ace/theme/monokai");
  this.editor.commands.addCommand({
    name: 'save',
    bindKey: {
      mac: 'Command-S',
      win: 'Ctrl-S',     // In Ace, "win" = "not mac"
    },
    exec: function(editor) {
      var curr_tab = this.tabs[this.find_tab_by_session(editor.getSession())];
      this.push_file_contents(curr_tab.file);
    }.bind(this),
    readOnly: false,
  });

  this.ui.tabctl.tabs({
    active: 1,
    activate: function(event, ui) {
      var tab = this.tabs[this.find_tab_by_id(ui.newTab.attr('tid'))];
      this.active = tab;
      this.refresh_editor();
      this.editor.focus();
    }.bind(this),
  });
  this.ui.tabctl.find(".ui-tabs-nav").sortable({
    axis: "x",
    stop: function() {
      this.ui.tabctl.tabs("refresh");
    }.bind(this),
  });
  this.ui.tabctl.delegate("span.ui-icon-close", "click", function() {
    var tid = $(this).closest("li").attr('tid');
    ws.close_tab_by_id(parseInt(tid));
  });

  this.refresh_editor();
}

Workspace.prototype.load = function() {
  $(".modal").on('shown.bs.modal', function(e) {
    $(':input:enabled:visible:first').focus();
  });
  set_up_csrf_token();
  this.load_projects();
  this.load_editor();
}

/* ---------------------------------------------------------------- */
Workspace.prototype.find_project_by_id = function(id) {
  return find(function(proj) { return proj.id == id }, this.projects);
}

Workspace.prototype.find_file_by_id = function(id) {
  for (var i = 0; i < this.projects.length; ++i) {
    var project = this.projects[i];
    for (var j = 0; j < project.files.length; ++j) {
      if (project.files[j].id == id)
        return project.files[j];
    }
  }
}
Workspace.prototype.find_tab_by_session = function(session) {
  return find_idx(function(tab) { return tab.session == session}, this.tabs);
}
Workspace.prototype.find_tab_by_file_id = function(id) {
  return find_idx(function(tab) { return tab.file.id == id }, this.tabs);
}
Workspace.prototype.find_tab_by_id = function(id) {
  return find_idx(function(tab) { return tab.id == id }, this.tabs);
}

/* ---------------------------------------------------------------- */
Workspace.prototype.add_tab = function(tab) {
  var tab_li   = $('<li>').attr('tid', tab.id);
  var tab_a    = $('<a>').attr('href', "#jqueryui-editor").text(tab.display);
  var tab_span = $('<span>').addClass("ui-icon ui-icon-close").attr('role', "presenstation");
  tab_li.append(tab_a,tab_span);
  this.ui.tabctl.children("ul").append(tab_li);
  this.ui.tabctl.tabs('refresh');

  tab.ui = tab_li;
  this.tabs.push(tab);
}

Workspace.prototype.new_tab_from_file = function(file) {
  file.session = ace.createEditSession(file.contents || "<loading>");
  file.session.setMode("ace/mode/javascript");        // TODO easycrypt
  var tab = new Tab(file.id, file.session, file);
  this.add_tab(tab);
}

Workspace.prototype.activate_tab = function(index) {
  this.ui.tabctl.tabs('option', 'active', index);
}

Workspace.prototype.close_tab_by_id = function(id) {
  var idx = this.find_tab_by_id(id);
  if (idx != -1) {
    this.tabs[idx].ui.remove();
    this.ui.tabctl.tabs("refresh");
    this.tabs.splice(idx, 1);
    if (this.tabs.length == 0) this.active = null;
    this.refresh_editor();
  }
}

/* ---------------------------------------------------------------- */
Workspace.prototype.open_file = function(id) {
  if (!(file = this.find_file_by_id(id)))
    return ;
  if ((tab = this.find_tab_by_file_id(file.id)) < 0) {
    this.new_tab_from_file(file);
    tab = this.tabs.length-1;
  }
  this.activate_tab(tab);
}

/*                             CALLBACKS                            */
/* ---------------------------------------------------------------- */
Workspace.prototype._callback_for_open_file_by_id = function(id) {
  return (function() { this.open_file(id); }).bind(this);
}

Workspace.prototype._callback_for_toggle_glyph = function(proj, glyph) {
  return function() {
    proj.is_unfolded = !proj.is_unfolded;
    glyph.toggleClass('glyphicon-chevron-up glyphicon-chevron-down');
  };
}

Workspace.prototype._callback_for_rm_file = function(id) {
  return (function() {
    $.ajax({
      url: 'files/' + id,
      type: 'DELETE',
      success: function() {
        var tab = this.tabs[this.find_tab_by_file_id(id)];
        this.close_tab_by_id(tab.id);
        this.load_projects();
      }.bind(this)
    });
  }).bind(this);
}

Workspace.prototype._callback_for_add_file_modal = function(id) {
  return (function() {
    var modal = $('#newfilemodal');
    var form = $('#newfilemodal form');
    var ws = this;
    form.each (function() { this.reset(); });
    form.one('submit', function(e) {
      $.ajax({
        url: "/ec/projects/" + id + "/files",
        data: $(this).serialize(),
        type: 'POST',
        success: function(data) {
          modal.modal('hide');
          ws.load_projects();
        },
      });
      e.preventDefault();
    });
    modal.modal();
  }).bind(this);
}

/* ---------------------------------------------------------------- */
var ws = null;

function ec_initialize() {
  ws = new Workspace();
}

$(document).ready(ec_initialize);
