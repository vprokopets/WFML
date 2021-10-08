#!/bin/bash

# Output colors
NORMAL="\\033[0;39m"
RED="\\033[1;31m"
BLUE="\\033[1;34m"

mode=


log() {
  echo -e "$BLUE > $1 $NORMAL"
}

error() {
  echo ""
  echo -e "$RED >>> ERROR - $1$NORMAL"
}

help() {
  echo "-----------------------------------------------------------------------"
  echo "-                 WFML deployment control script                       -"
  echo "-                                                                      -"
  echo "-                      Available commands:                             -"
  echo "-----------------------------------------------------------------------"
  echo -e -n "$BLUE"
  echo "   > up - Starts WFML django server on 127.0.0.1:8000."
  echo "        Optional parameter:"
  echo "        --mode or -m: A parameter that specifies running mode. "
  echo "                * docker-compose:  Running WFML by docker-compose using bridge networking mode."
  echo
  echo "   > down - Stops WFML django server on 127.0.0.1:8000. Please, note that this command will affect all the runserver processes."
  echo "        Optional parameter:"
  echo "        --mode or -m: A parameter that specifies stopping mode. "
  echo "                * docker-compose:  Stopping WFML by docker-compose."
  echo
  echo "   > restart - sequential execution of 'down' and 'up' commands."
  echo
  echo "   > help - Display this help message."
  echo -e -n "$NORMAL"
  echo "-----------------------------------------------------------------------"
  echo "- For more information refer to https://github.com/vprokopets/WFML -"
  echo "-----------------------------------------------------------------------"

}

up() {
  if [[ "${mode}" == "docker-compose" ]]; then
        log "Building and deploying WFML to docker-compose."
        docker-compose build 
        log "Starting..."
        docker-compose up -d
  else
        python3 manage.py runserver
  fi
}

down() {
  if [[ "${mode}" == "docker-compose" ]] || [[ "${mode}" == "docker-compose-remote" ]]; then
        log "Stopping docker-compose deployment of WFML..."
        docker-compose down
   else
        pkill -f runserver
   fi
}

restart(){
    log "Restarting WFML."
    down
    up
}

if [[ -z ${1}  ]]; then
  help
else
    command=$1
    shift
while [[ "$1" != "" ]]; do
        case $1 in
            -m | --mode )
                shift
                mode=$1
                if [[ "${mode}" != "docker-compose" ]]; then
                    error "Wrong parameter --mode (-m)"
                    help
                    exit 1
                fi
                ;;
            * )
                help
                exit 1
        esac
        shift
    done
fi

${command}
