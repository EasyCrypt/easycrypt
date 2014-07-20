from django.db import models
from django.contrib.auth import get_user_model


class Project(models.Model):
    name = models.CharField(max_length=200)
    owner = models.ForeignKey(get_user_model())

    def __unicode__(self):
        return self.name


class File(models.Model):
    name = models.CharField(max_length=200)
    contents = models.TextField()
    project = models.ForeignKey(Project)

    def __unicode__(self):
        return self.name
