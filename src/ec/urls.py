from django.conf.urls import patterns, url

from ec import views

urlpatterns = patterns('',
   url(r'^$', views.index, name='index'),
   url(r'^register/$', views.register, name='register'),
   url(r'^login/$', views.login, name='login'),
   url(r'^logout/$', views.logout, name='logout'),

   # Information retrieval from the client (not meant for user interaction)
   url(r'^projects/$', views.get_projects, name='get_projects'),
   url(r'^projects/create$', views.create_project, name='create_project'),
   url(r'^projects/(?P<proj_id>\d+)/files/create$', views.create_file,
       name='create_file'),
   url(r'^files/(?P<file_id>\d+)/contents$', views.file_contents,
       name='file_contents'),
   url(r'^files/(?P<file_id>\d+)/rm$', views.rm_file,
       name='rm_file'),
)
