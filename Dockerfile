FROM ubuntu:20.04

# Updating the system and adding python3
RUN apt-get update && apt-get install -y -qq \
    python3-pip \
    && apt-get -qq clean \
    && apt-get -qq autoremove \
    && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*


# Installing project requirements
COPY requirements.txt /root
RUN python3 -m pip install --no-cache-dir -q -r /root/requirements.txt

# Copying project
COPY . /root
RUN rm /root/Dockerfile

WORKDIR /root
RUN python3 manage.py makemigrations
RUN python3 manage.py migrate