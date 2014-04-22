from django.shortcuts import render
from django.http import HttpResponse, HttpResponseRedirect
from django.core import serializers
from django.core.urlresolvers import reverse
from django.contrib import auth

#from django.views import generic

from ec.forms import RegisterForm, LoginForm


def index(request):
    if request.user.is_authenticated():
        project_list = request.user.project_set.all()
    else:
        project_list = []

    return render(request, 'ec/index.html', {'project_list': project_list})


def register(request):
    if request.method == 'POST':
        form = RegisterForm(request.POST)
        if form.is_valid():
            form.save()
            return HttpResponseRedirect(reverse('ec:index'))
        else:
            return render(request, 'ec/register.html', {'form': form})
    else:
        form = RegisterForm()
        return render(request, 'ec/register.html', {'form': form})


def login(request):
    if request.method == 'POST':
        form = LoginForm(request, request.POST)
        if form.is_valid():
            user = form.get_user()
            auth.login(request, user)
            return HttpResponseRedirect(reverse('ec:index'))
        else:
            return render(request, 'ec/login.html', {'form': form})
    else:
        form = LoginForm(request)
        return render(request, 'ec/login.html', {'form': form})


def logout(request):
    auth.logout(request)
    return HttpResponseRedirect(reverse('ec:index'))


def get_projects(request):
    if request.user.is_authenticated():
        resp = serializers.serialize('json', request.user.project_set.all())
        return HttpResponse(resp, content_type="application/json")
    else:
        return HttpResponse('Unauthorized', status=401)
