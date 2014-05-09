from django.shortcuts import render, get_object_or_404
from django.http import HttpResponse, HttpResponseRedirect
from django.core.urlresolvers import reverse
from django.contrib import auth
from django.contrib.auth.decorators import login_required
import json

#from django.views import generic

from ec.models import File, Project

from ec.forms import RegisterForm, LoginForm
from ec.forms import ProjectCreationFormModal, FileCreationFormModal


def _json_HttpResponse(resp):
    return HttpResponse(json.dumps(resp), content_type="application/json")


def index(request):
    return render(request, 'ec/index.html',
                  {'newprojform': ProjectCreationFormModal(),
                   'newfileform': FileCreationFormModal()})


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


@login_required
def get_projects(request):
    dbprojects = request.user.project_set.all()
    projects = []

    for dbproject in dbprojects:
        dbfiles = File.objects.filter(project=dbproject.id)
        files = [dict(id=x.id, name=x.name) for x in dbfiles]
        projects.append(dict(id=dbproject.id,
                             name=dbproject.name,
                             files=files))

    return _json_HttpResponse(projects)


@login_required
def create_project(request):
    if request.method == 'POST':
        form = ProjectCreationFormModal(request.POST)
        if form.is_valid():
            proj = Project(name=form.cleaned_data['proj_name'],
                           owner=request.user)
            proj.save()
            return HttpResponseRedirect(reverse('ec:index'))
        else:
            return HttpResponse(str(form.errors), status=400)
    else:
        return HttpResponse('Only POST method allowed', status=405)


@login_required
def create_file(request, proj_id):
    if request.method == 'POST':
        form = FileCreationFormModal(request.POST)
        if form.is_valid():
            proj = get_object_or_404(Project, pk=proj_id)
            f = File(name=form.cleaned_data['file_name'],
                     contents=form.cleaned_data['file_contents'], project=proj)
            f.save()
            return HttpResponseRedirect(reverse('ec:index'))
        else:
            return HttpResponse(str(form.errors), status=400)
    else:
        return HttpResponse('Only POST method allowed', status=405)


@login_required
def get_file_contents(request, file_id):
    f = get_object_or_404(File, pk=file_id)
    return _json_HttpResponse(f.contents)


@login_required
def rm_file(request, file_id):
    f = get_object_or_404(File, pk=file_id)
    f.delete()
    return HttpResponse('OK', status=200)
