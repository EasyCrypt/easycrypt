from django import forms
from django.core.urlresolvers import reverse
from django.contrib.auth.forms import UserCreationForm, AuthenticationForm
from django.utils.translation import ugettext_lazy as _
from crispy_forms.helper import FormHelper
from crispy_forms.layout import Submit, Button, Layout, Field, Div
from crispy_forms.bootstrap import FormActions


def _field_set_attr(self, field, attr):
    self.fields[field].widget.attrs[attr] = unicode(attr)


def require(self, fields):
    for field in fields:
        _field_set_attr(self, field, 'required')


def autofocus(self, field):
    _field_set_attr(self, field, 'autofocus')


class RegisterForm(UserCreationForm):
    username = forms.RegexField(
        label=(""), max_length=30,
        regex=r'^\w+$',
        error_messages={'invalid':
                        _("This value may contain only letters, "
                          "underscores and numbers.")})

    password1 = forms.CharField(
        label=(""),
        widget=forms.PasswordInput)

    password2 = forms.CharField(
        label=(""),
        widget=forms.PasswordInput)

    def __init__(self, *args, **kwargs):
        super(RegisterForm, self).__init__(*args, **kwargs)

        self.helper = FormHelper()
        self.helper.form_action = reverse('ec:register')
        self.helper.form_class = "form form-register form-centered"
        self.helper.layout = Layout(
            Field('username', placeholder="Username",
                  css_class="form-control fld-mg-bot"),
            Field('password1', placeholder="Password",
                  css_class="form-control fld-seq-fst"),
            Field('password2', placeholder="Repeat password",
                  css_class="form-control fld-seq-lst"),
            FormActions(Submit('register', 'Register',
                    css_class="btn btn-lg btn-primary btn-block fld-mg-top")
            )
        )

        require(self, ['username', 'password1', 'password2'])
        autofocus(self, 'username')


class LoginForm(AuthenticationForm):
    username = forms.RegexField(
        label=(""), max_length=30,
        regex=r'^\w+$',
        error_messages={'invalid':
                        _("This value may contain only letters, "
                          "underscores and numbers.")})

    password = forms.CharField(
        label=(""),
        widget=forms.PasswordInput)

    def __init__(self, *args, **kwargs):
        super(LoginForm, self).__init__(*args, **kwargs)

        self.helper = FormHelper()
        self.helper.form_action = reverse('ec:login')
        self.helper.form_class = "form form-centered"
        self.helper.layout = Layout(
            Field('username', placeholder="Username",
                  css_class="form-control fld-seq-fst"),
            Field('password', placeholder="Password",
                  css_class="form-control fld-seq-lst"),
            FormActions(Submit('login', 'Log in',
                    css_class="btn btn-lg btn-primary btn-block fld-mg-top")
            )
        )

        require(self, ['username', 'password'])
        autofocus(self, 'username')


class ProjectCreationFormModal(forms.Form):
    proj_name = forms.RegexField(
        label=(""), max_length=30,
        regex=r'^[a-zA-Z0-9_ ]+$',
        error_messages={'invalid':
                        _("This value may contain only letters, "
                          "underscores, spaces and numbers.")})

    def __init__(self, *args, **kwargs):
        super(ProjectCreationFormModal, self).__init__(*args, **kwargs)

        self.helper = FormHelper()
        self.helper.form_action = reverse('ec:projects')
        self.helper.form_class = "form form-centered"
        self.helper.layout = Layout(
            Div(Field('proj_name', placeholder="Project name",
                      css_class="form-control"),
                css_class="modal-body"),
            Div(FormActions(Button('proj_cancel', 'Cancel',
                                   css_class="btn btn-default",
                                   data_dismiss="modal"),
                            Submit('proj_create', 'New project',
                                   css_class="btn btn-primary")),
                css_class="modal-footer"),
        )

        require(self, ['proj_name'])
        autofocus(self, 'proj_name')


class FileCreationFormModal(forms.Form):
    file_name = forms.RegexField(
        label=(""), max_length=30,
        regex=r'^[a-zA-Z0-9_ ]+$',
        error_messages={'invalid':
                        _("This value may contain only letters, "
                          "underscores, spaces and numbers.")})

    def __init__(self, *args, **kwargs):
        super(FileCreationFormModal, self).__init__(*args, **kwargs)

        self.helper = FormHelper()
        self.helper.form_class = "form"
        self.helper.layout = Layout(
            Div(Field('file_name', placeholder="File name",
                      css_class="form-control"),
                css_class="modal-body"),
            Div(FormActions(Button('file_cancel', 'Cancel',
                                   css_class="btn btn-default",
                                   data_dismiss="modal"),
                            Submit('file_create', 'New file',
                                   css_class="btn btn-primary")),
                css_class="modal-footer"),
        )

        require(self, ['file_name'])
        autofocus(self, 'file_name')
