$(document).ready(function() {

/* Project class */
var Project = function(id, name) {
	this.id = id
	this.name = name
}

/* Workspace object (state) */
var ws = {
	projects: [],
	curr_project: null,
	tabs: [],
	curr_tab: null,

//	/* Update the frontend */
//	sync: function() {
//		
//	}
}

/* Load project data */
$.get('projects/', function(ps) {
	function parseProject(p) {
		return new Project(p.pk, p.fields.name)
	}
	ws.projects = map(parseProject, ps);
})

/* Project click callback */
$('#projects li a').on('click', function() {
	var my_id = parseInt($(this).parent().attr('project_id'));
	ws.curr_project = find(function (p) { return p.id === my_id }, ws.projects);
//	ws.sync();
});

//$('#projects li a').on('click',
//function() {
//$(this).parent().parent().children('.active').removeClass('active');
//$(this).parent().addClass('active');
//});

var tabs = $('#tabs');

/* Tab click callback (load file contents) */
var file_contents = $("#file-contents");
function set_file_contents(use_this) {
	return function() {
		var source = use_this ? $(this) : tabs.children('.active').children();
		var id = source.parent().attr('file_id');
		var name = source.html();
		file_contents.val("<contents of " + name + " (id=" + id + ")>");
	};
};

function set_tab_click_callback() {
	$('#tabs li a').click(set_file_contents(true));
};
set_tab_click_callback();

/* File click callback: open new tab or change focus */
$('.project-files li a').click(
	function() {
		var id = $(this).parent().attr('file_id');
		var matching_tabs = tabs.children("li[file_id='" + id + "']");
		if (matching_tabs.length == 1) {
			tabs.children('.active').removeClass('active');
			matching_tabs.addClass('active');
		} else {
			tabs.children('.active').removeClass('active');
			tabs.append('<li class="active" file_id="' + id
					+ '"><a data-toggle="pill" href="#">'
					+ $(this).html() + '</a></li>');
			set_tab_click_callback();
		}
		set_file_contents(false)();
	});
});
