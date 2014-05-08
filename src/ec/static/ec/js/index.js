/* ---------------------------------------------------------------- */
var Project = function(id, name) {
  this.id    = id;
  this.name  = name;
  this.files = [];
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
  this.projects = null;
  this.tabs     = [];
  this.active   = null; /* index of the active tab */

  this.ui = {}
  this.ui.tabs     = $('#tabs');
  this.ui.contents = $('#file-contents');
  this.ui.treeview = $('#projects');

  this.load();
}

/* ---------------------------------------------------------------- */
Workspace.prototype.reset_ui = function() {
  this.ui.tabs.children().remove();
  this.ui.treeview.children().remove();
  this.refresh_contents();
}

/* ---------------------------------------------------------------- */
Workspace.prototype.load = function() {
  $.get('projects/', function(ps) {
    this.reset_ui();
    this.projects = ps.map(function(p) {
      var project = new Project(p.id, p.name);
      for (var i = 0; i < p.files.length; ++i) {
        var file = p.files[i];
        project.files.push(new File(file.id, file.name, null, p));
      }
      return project;
    });

    for (var i = 0; i < this.projects.length; ++i) {
      var project = this.projects[i];

      var expand_proj = glyph('glyphicon-chevron-up');
      var target_id = "proj_files_" + i
      expand_proj.attr('data-toggle', 'collapse').attr('data-target', '#'+target_id);
      var files_col = col(11, 1).addClass('collapse').attr('id', target_id);

      var toggle_glyph = this._callback_for_toggle_glyph(expand_proj);
      files_col.on('shown.bs.collapse', toggle_glyph);
      files_col.on('hidden.bs.collapse', toggle_glyph);
      
      // TODO The collapse logic should be controlled from the Project models

      for (var j = 0; j < project.files.length; ++j) {
        var file      = project.files[j];
        var filelink  = $('<a>').text(file.name);
        filelink.on('click', this._callback_for_open_by_id(file.id));
        var rm_but = glyph('glyphicon-remove pull-right red');
        rm_but.on('click', this._callback_for_rm_file(file.id));
        files_col.append(row(filelink, rm_but));
      }
      files_col.append(row(glyph('glyphicon-plus')));

      var project_tree =
        row(col(12,0, row(expand_proj, " ", project.name),
                      row(files_col),
                      $('<hr />')));

      this.ui.treeview.append(project_tree);
    }
  }.bind(this));
}

/* ---------------------------------------------------------------- */
Workspace.prototype.load_ui = function() {
  ws = new Workspace()
}

/* ---------------------------------------------------------------- */
Workspace.prototype.find_file_by_id = function(id) {
  for (var i = 0; i < this.projects.length; ++i) {
    var project = this.projects[i]
    for (var fileidx = 0; fileidx < project.files.length; ++fileidx) {
      if (project.files[fileidx].id == id)
        return project.files[fileidx];
    }
  }
}

/* ---------------------------------------------------------------- */
Workspace.prototype.find_tab_for_file_id = function(id) {
  for (var i = 0; i < this.tabs.length; ++i) {
    if (this.tabs[i].file.id == id)
      return i;
  }
  return -1;
}

/* ---------------------------------------------------------------- */
Workspace.prototype.refresh_contents = function() {
  if (this.active != null) {
    var current_file = this.tabs[this.active].file;
    this.ui.contents.val(current_file.contents);
    if (current_file.is_loading)
      this.ui.contents.attr('disabled','disabled');
    else
      this.ui.contents.removeAttr('disabled');
  } else {
    this.ui.contents.val("");
    this.ui.contents.attr('disabled', 'disabled');
  }
}

/* ---------------------------------------------------------------- */
Workspace.prototype.set_contents = function(id) {
  if (!(file = this.find_file_by_id(id)))
    return ;
  if (!file.contents) {
    file.is_loading = true;
    file.contents = "loading...";
    $.get('files/' + file.id + "/contents", (function (file,contents) {
      file.contents = contents;
      file.is_loading = false;
      this.refresh_contents();
    }).bind(this,file));
  }
  this.refresh_contents();
}

/* ---------------------------------------------------------------- */
Workspace.prototype.append_new_tab = function(file) {
  this.tabs.push(new Tab(file));

  var node = $('<li>');
  var link = $('<a>').text(file.name);

  node.append(link);
  this.ui.tabs.append(node);

  link.on('click', this._callback_for_activate_tab_by_index(this.tabs.length-1));
}

/* ---------------------------------------------------------------- */
Workspace.prototype.activate_tab = function(index) {
  if (index > this.tabs.length-1)
    return ;
  this.active = index;
  this.ui.tabs.find('.active').removeClass('active');
  this.ui.tabs.find(':nth-child(' + (index+1) + ')').addClass('active');
  this.set_contents(this.tabs[index].file.id);
}

/* ---------------------------------------------------------------- */
Workspace.prototype.open = function(id) {
  if (!(file = this.find_file_by_id(id)))
    return ;
  if ((filetab = this.find_tab_for_file_id(file.id)) < 0) {
    this.append_new_tab(file);
  }
  this.activate_tab(filetab < 0 ? this.tabs.length-1 : filetab);
}

/* ---------------------------------------------------------------- */
Workspace.prototype._callback_for_open_by_id = function(id) {
  return (function() { this.open(id); }).bind(this);
}

/* ---------------------------------------------------------------- */
Workspace.prototype._callback_for_set_contents_by_id = function(id) {
  return (function() { this.set_contents(id); }).bind(this);
}

/* ---------------------------------------------------------------- */
Workspace.prototype._callback_for_activate_tab_by_index = function(index) {
  return (function() { this.activate_tab(index); }).bind(this);
}

/* ---------------------------------------------------------------- */
Workspace.prototype._callback_for_toggle_glyph = function(glyph) {
  return function() {
    glyph.toggleClass('glyphicon-chevron-up glyphicon-chevron-down');
  };
}

/* ---------------------------------------------------------------- */
Workspace.prototype._callback_for_rm_file = function(id) {
  return (function () {
    $.get('files/' + id + '/rm', ec_initialize);
  }).bind(this);
}

/* ---------------------------------------------------------------- */
var ws = null;

function ec_initialize() {
  ws = new Workspace();
}

$(document).ready(ec_initialize);
