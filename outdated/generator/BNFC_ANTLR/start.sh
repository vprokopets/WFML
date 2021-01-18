cd /usr/local/lib
sudo wget https://www.antlr.org/download/antlr-4.9-complete.jar
export CLASSPATH=".:/usr/local/lib/antlr-4.9-complete.jar:$CLASSPATH"
alias antlr4='java -jar /usr/local/lib/antlr-4.9-complete.jar'
alias grun='java org.antlr.v4.gui.TestRig'
