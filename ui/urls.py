from django.urls import path
from ui.views import factory_wizard, initial_page, download_file

urlpatterns = [
    path('configure/', factory_wizard, name='factory_wizard'),
    path('initialize/', initial_page, name='initial_page'),
    path('download/', download_file, name='download_file'),
]
