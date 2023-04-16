from django.urls import path, re_path
from ui.views import download_modelica_file, factory_wizard, initial_page, download_file, redirect_to_homepage, use_pn_models

urlpatterns = [
    path('configure/', factory_wizard, name='factory_wizard'),
    path('initialize/', initial_page, name='initial_page'),
    path('download/', download_file, name='download_file'),
    path('pn-models/', use_pn_models, name=' pn_models'),
    path('get-pnmodel/', download_modelica_file, name='download_om_file'),
    re_path(r'download?.+', download_file, name='download_file'),
    re_path(r'get-pnmodel?.+', download_modelica_file, name='download_om_file'),
    re_path(r'^', redirect_to_homepage, name='redirect_to_homepage')
]
