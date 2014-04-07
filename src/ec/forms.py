from django import forms
from django.core.urlresolvers import reverse
from django.contrib.auth.forms import UserCreationForm, AuthenticationForm
from django.utils.translation import ugettext_lazy as _
from crispy_forms.helper import FormHelper
from crispy_forms.layout import Submit, Layout, Field
from crispy_forms.bootstrap import FormActions


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
        super(RegisterForm, self).__init__(*args, **kwargs)


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
        super(LoginForm, self).__init__(*args, **kwargs)
