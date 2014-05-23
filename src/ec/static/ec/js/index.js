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

  this.is_loading = false;
}

/* ---------------------------------------------------------------- */
var Tab = function(file, display) {
  this.file    = file;
  this.display = display || file.name;
}

/* ---------------------------------------------------------------- */
var Workspace = function() {
  this.ui       = null;
  this.projects = [];
  this.tabs     = [];
  this.active   = null; /* index of the active tab */

  this.editor   = null;

  this.ui = {}
  this.ui.tabs     = $('#tabs');
  this.ui.treeview = $('#projects');

  this.load();
}

/* ---------------------------------------------------------------- */
Workspace.prototype.current_file = function() {
  if (this.active != null)
    return this.tabs[this.active].file;
  else
    return null;
}

/* ---------------------------------------------------------------- */
Workspace.prototype.get_file_contents = function(file) {
  file.is_loading = true;
  file.contents = "loading...";
  $.get('files/' + file.id, (function (file,contents) {
    file.contents = contents;
    file.is_loading = false;
    this.refresh_editor();
  }).bind(this,file));
}

Workspace.prototype.push_file_contents = function(file) {
  $.post('files/' + file.id, {contents:file.contents});
}

/* ---------------------------------------------------------------- */
Workspace.prototype.refresh_editor = function() {
  var current_file = this.current_file();
  if (current_file != null) {
    if (!current_file.contents) {
      this.get_file_contents(current_file);
    }
    this.editor.setValue(current_file.contents);
    this.editor.setReadOnly(current_file.is_loading);
  } else {
    this.editor.setValue("");
    this.editor.setReadOnly(true);
  }
}

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

Workspace.prototype.refresh_tabs = function() {
  this.ui.tabs.children().remove();
  for (var i = 0; i < this.tabs.length; ++i) {
    var tab = this.tabs[i];

    var node = $('<li>');
    if (i === this.active) node.addClass('active');

    var link = $('<a>').text(tab.display);
    link.on('click', this._callback_for_activate_tab_by_index(i));

    node.append(link);
    this.ui.tabs.append(node);
  }
}

Workspace.prototype.refresh_ui = function() {
  this.refresh_editor();
  this.refresh_projects();
  this.refresh_tabs();
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
    this.refresh_ui();
  }.bind(this));
}

Workspace.prototype.load_editor = function() {
  this.editor = ace.edit("editor");
  this.editor.setTheme("ace/theme/monokai");
  this.editor.getSession().setMode("ace/mode/javascript");
}

Workspace.prototype.load = function() {
  $("#close-tab").on('click', function() {
    this.close_tab_by_index(this.active);
    this.refresh_tabs();
    this.refresh_editor();
  }.bind(this));
  $(".modal").on('shown.bs.modal', function(e) {
    $(':input:enabled:visible:first').focus();
  });
  set_up_csrf_token();
  this.load_editor();
  this.load_projects();
}

/* ---------------------------------------------------------------- */
Workspace.prototype.find_project_by_id = function(id) {
  for (var i = 0; i < this.projects.length; ++i) {
    var project = this.projects[i];
    if (project.id == id)
      return project;
  }
}

/* ---------------------------------------------------------------- */
Workspace.prototype.find_file_by_id = function(id) {
  for (var i = 0; i < this.projects.length; ++i) {
    var project = this.projects[i];
    for (var j = 0; j < project.files.length; ++j) {
      if (project.files[j].id == id)
        return project.files[j];
    }
  }
}
Workspace.prototype.find_tab_for_file_id = function(id) {
  for (var i = 0; i < this.tabs.length; ++i) {
    if (this.tabs[i].file.id == id)
      return i;
  }
  return -1;
}

/* ---------------------------------------------------------------- */
Workspace.prototype.close_tab_by_index = function(tab) {
  if (tab >= 0) {
    this.tabs.splice(tab, 1);
    if (this.tabs.length === 0) this.active = null;
    else if (this.active > this.tabs.length-1) --this.active;
  }
}

Workspace.prototype.close_tab_by_file_id = function(id) {
  if ((index = this.find_tab_for_file_id(id)) >= 0) {
    this.close_tab_by_index(index);
  }
}

/* ---------------------------------------------------------------- */
Workspace.prototype.activate_tab = function(index) {
  if (index > this.tabs.length-1)
    return ;
  if (this.active != null && index != this.active) {
    var current_file = this.current_file();
    current_file.contents = this.editor.getValue();
    this.push_file_contents(current_file);
  }
  this.active = index;
  this.refresh_tabs();
  this.refresh_editor();
}

/* ---------------------------------------------------------------- */
Workspace.prototype.open_file = function(id) {
  if (!(file = this.find_file_by_id(id)))
    return ;
  if ((filetab = this.find_tab_for_file_id(file.id)) < 0) {
    this.tabs.push(new Tab(file));
    this.activate_tab(this.tabs.length-1);
  } else {
    this.activate_tab(filetab);
  }
}

/*                             CALLBACKS                            */
/* ---------------------------------------------------------------- */
Workspace.prototype._callback_for_open_file_by_id = function(id) {
  return (function() { this.open_file(id); }).bind(this);
}

Workspace.prototype._callback_for_activate_tab_by_index = function(index) {
  return (function() { this.activate_tab(index); }).bind(this);
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
        this.close_tab_by_file_id(id);
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
