from django.conf.urls import patterns, url

from ec import views

urlpatterns = patterns('',
   url(r'^$', views.index, name='index'),
   url(r'^register/$', views.register, name='register'),
   url(r'^login/$', views.login, name='login'),
   url(r'^logout/$', views.logout, name='logout'),

   # Information retrieval from the client (not meant for user interaction)
   url(r'^projects/$', views.get_projects, name='get_projects'),
   url(r'^files/(?P<file_id>\d+)/contents$', views.get_file_contents,
       name='get_file_contents'),
)
