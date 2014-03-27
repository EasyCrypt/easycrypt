from django.shortcuts import render, get_object_or_404
from django.http import HttpResponseRedirect, Http404
from django.core.urlresolvers import reverse
from django.views import generic
from django.utils import timezone

from polls.forms import ContactForm, DetailForm
from polls.models import Poll, Choice


class IndexView(generic.ListView):
    template_name = 'polls/index.html'
    context_object_name = 'latest_poll_list'

    def get_queryset(self):
        """Return the last five published polls."""
        return Poll.objects.filter(
            pub_date__lte=timezone.now()
        ).order_by('-pub_date')[:5]


def detail(request, pk):
    p = get_object_or_404(Poll, pk=pk)
    form = DetailForm(poll=p)
    if p.pub_date <= timezone.now():
        return render(request, 'polls/detail.html', {'form': form})
    else:
        raise Http404


class ResultsView(generic.DetailView):
    model = Poll
    template_name = 'polls/results.html'


def vote(request, poll_id):
    p = get_object_or_404(Poll, pk=poll_id)
    try:
        selected_choice = p.choice_set.get(pk=request.POST['choices'])
    except (KeyError, Choice.DoesNotExist):
        form = DetailForm(poll=p)
        return render(request, 'polls/detail.html',
            {'form': form, 'error_message': "You didn't select a choice."})
    else:
        selected_choice.votes += 1
        selected_choice.save()
        return HttpResponseRedirect(reverse('polls:results', args=(p.id,)))


def contact(request):
    if request.method == 'POST':
        form = ContactForm(request.POST)
        if form.is_valid():
            return HttpResponseRedirect(reverse('polls:contact'))
    else:
        form = ContactForm()
    return render(request, 'polls/contact.html', {'form': form})
