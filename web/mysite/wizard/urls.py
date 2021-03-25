from django.urls import path

from wizard.forms import Form1, Form2
from wizard.views import ChoiceWizardView, factory_wizard, initial_page, WizardClass


urlpatterns = [
    path('', ChoiceWizardView.as_view([Form1, Form2])),
    path('create_wizard/', factory_wizard, name='factory_wizard'),
    path('test/', initial_page, name='initial_page'),
]
