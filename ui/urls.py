from django.urls import path, re_path
from ui.views import factory_wizard, initial_page, download_file, MyWizardView

from django.shortcuts import render


urlpatterns = [
    path('configure/', factory_wizard, name='factory_wizard'),
    path('initialize/', initial_page, name='initial_page'),
    path('download/', download_file, name='download_file'),
    re_path(r'download?.+', download_file, name='download_file'),
    path('test/<int:step>/', MyWizardView.as_view(), name='wizard_form'),
    path('test/', MyWizardView.as_view(), name='wizard_form'),
]
