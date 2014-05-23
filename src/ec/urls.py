from django.conf.urls import patterns, url

from ec import views

urlpatterns = patterns('',
   url(r'^$', views.index, name='index'),
   url(r'^register/$', views.register, name='register'),
   url(r'^login/$', views.login, name='login'),
   url(r'^logout/$', views.logout, name='logout'),

   # Information retrieval from the client (not meant for user interaction)
   url(r'^projects$', views.projects, name='projects'),
   url(r'^projects/(?P<proj_id>\d+)/files$', views.project_files,
       name='project_files'),
   url(r'^files/(?P<file_id>\d+)$', views.file_, name='file'),
)
