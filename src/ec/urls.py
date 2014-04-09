from django.conf.urls import patterns, url

from ec import views

urlpatterns = patterns('',
   url(r'^$', views.index, name='index'),
   url(r'^register/$', views.register, name='register'),
   url(r'^login/$', views.login, name='login'),
   url(r'^logout/$', views.logout, name='logout'),
)
