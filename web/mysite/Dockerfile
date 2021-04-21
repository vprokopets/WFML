FROM ubuntu:18.04

# Updating the system and adding python3
RUN apt-get update && apt-get install -y -qq \
    python3.7 \
    python3-pip \
    python3.7-dev \
    && apt-get -qq clean \
    && apt-get -qq autoremove \
    && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*


# Installing project requirements
COPY requirements.txt /root
RUN python3.7 -m pip install --no-cache-dir -q -r /root/requirements.txt

# Copying project
COPY . /root
RUN rm /root/Dockerfile

WORKDIR /root
RUN python3.7 manage.py makemigrations
RUN python3.7 manage.py migrate