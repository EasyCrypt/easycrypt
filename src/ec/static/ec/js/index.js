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
Workspace.prototype.load = function() {
  $.get('projects/', function(ps) {
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

      var toggle_col = $('<div>').addClass('col-sm-3 col-md-2');
      var toggle = $('<span>').addClass('glyphicon glyphicon-chevron-up');
      toggle.attr('data-toggle', 'collapse').attr('data-target', '#projfs_'+i);
      toggle_col.append(toggle);

      var proj_col  = $('<div>').addClass('col-sm-9 col-md-10');
      var name_row  = $('<div>').addClass('row').text(project.name);
      var files_row = $('<div>').addClass('row');
      proj_col.append(name_row, files_row);

      var proj_row   = $('<div>').addClass('row');
      proj_row.append(toggle_col, proj_col);
      
      this.ui.treeview.append(proj_row);
      if (project.files.length) {
        var subnode = $('<ul>').addClass('nav collapse');
        subnode.attr('id', 'projfs_'+i);
        var collapse_callback = this._callback_for_collapse(toggle);
        subnode.on('shown.bs.collapse', collapse_callback);
        subnode.on('hidden.bs.collapse', collapse_callback);

        files_row.append(subnode);
        for (var j = 0; j < project.files.length; ++j) {
          var file     = project.files[j];
          var filenode = $('<li>');
          var filelink = $('<a>').text(file.name);

          filenode.append(filelink);
          subnode .append(filenode);

          filelink.on('click', this._callback_for_open_by_id(file.id));
        }
      }
    }
  }.bind(this));
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
  var current_file = this.tabs[this.active].file;
  this.ui.contents.val(current_file.contents);
  if (current_file.is_loading)
    this.ui.contents.attr('disabled','disabled');
  else
    this.ui.contents.removeAttr('disabled');
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

Workspace.prototype._callback_for_collapse = function(toggle) {
  return function() { toggle.toggleClass('glyphicon-chevron-up glyphicon-chevron-down'); };
}

/* ---------------------------------------------------------------- */
var ws = null;

function ec_initialize() {
  ws = new Workspace();
}
    
$(document).ready(ec_initialize);
