from django.urls import path
from ui.views import factory_wizard, initial_page, done

urlpatterns = [
    path('create_wizard/', factory_wizard, name='factory_wizard'),
    path('test/', initial_page, name='initial_page'),
]
