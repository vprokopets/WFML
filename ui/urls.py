from django.urls import path, re_path
from ui.views import factory_wizard, initial_page, download_file, redirect_to_homepage, configure_metadata_output

urlpatterns = [
    path('configure/', factory_wizard, name='factory_wizard'),
    path('initialize/', initial_page, name='initial_page'),
    path('download/', download_file, name='download_file'),
    path('metadata/', configure_metadata_output, name='configure_metadata_output'),
    re_path(r'metadata?.+', configure_metadata_output, name='configure_metadata_output'),
    re_path(r'download?.+', download_file, name='download_file'),
    re_path(r'^', redirect_to_homepage, name='redirect_to_homepage')
]
