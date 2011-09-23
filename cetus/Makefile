JAVALOC?=/home/andrew/Downloads

ANTLR=$(JAVALOC)/install/lib/antlr.jar
JAVA=$(JAVALOC)/jdk1.6.0_27/bin/java
JAVAC=$(JAVALOC)/jdk1.6.0_27/bin/javac
JAR=$(JAVALOC)/jdk1.6.0_27/bin/jar
JAVADOC=$(JAVALOC)/jdk1.6.0_27/bin/javadoc

JFLAGS = -cp $(CLASSPATH):$(JAVALOC)/cetus-1.3/lib/cetus.jar:$(JAVALOC)/jdk1.6.0_27/lib:$(JAVALOC)/install/lib/antlr.jar:.

SOURCES = proj1.java LLVMCodeGenPass.java

all: $(SOURCES:.java=.class)

%.class : %.java
	javac $(JFLAGS) $<

test: all
	java $(JFLAGS) proj1 -verbosity=1 main.c

clean:
	rm -Rf *.class cetus_output *.ll *~
