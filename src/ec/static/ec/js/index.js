$(document).ready(function() {
var tabs = $('#tabs');

/* Project click callback */
$('#projects li a').on('click',
	function() {
	$(this).parent().parent().children('.active').removeClass('active');
	$(this).parent().addClass('active');
});

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
