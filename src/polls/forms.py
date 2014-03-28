from django import forms
from django.core.urlresolvers import reverse
from crispy_forms.helper import FormHelper
from crispy_forms.layout import Submit


class ContactForm(forms.Form):
    like_website = forms.TypedChoiceField(
        label="Do you like this website?",
        choices=((1, "Yes"), (0, "No")),
        coerce=lambda x: bool(int(x)),
        widget=forms.RadioSelect,
        initial='1',
        required=True,
    )

    favorite_food = forms.CharField(
        label="What is your favorite food?",
        max_length=80,
        required=True,
    )

    favorite_color = forms.CharField(
        label="What is your favorite color?",
        max_length=80,
        required=True,
    )

    favorite_number = forms.IntegerField(
        label="Favorite number",
        required=False,
    )

    notes = forms.CharField(
        label="Additional notes or feedback",
        required=False,
    )

    def __init__(self, *args, **kwargs):
        self.helper = FormHelper()
        self.helper.form_action = reverse('polls:contact')
        self.helper.add_input(Submit('submit', 'Submit'))
        super(ContactForm, self).__init__(*args, **kwargs)


class DetailForm(forms.Form):
    def __init__(self, poll, *args, **kwargs):
        self.poll = poll
        self.helper = FormHelper()
        self.helper.form_action = reverse('polls:vote', args=(self.poll.id,))
        self.helper.add_input(Submit('submit', 'Vote'))
        super(DetailForm, self).__init__(*args, **kwargs)
        if not 'choices' in self.fields:
            self.fields['choices'] = forms.ChoiceField(
                label="",
                widget=forms.RadioSelect,
                required=True,
                choices=[(str(idx), c.choice_text) for (idx, c) in
                         enumerate(self.poll.choice_set.all(), start=1)]
            )
