JAVALOC?=/usr/bin
ANTLRLOC?=/opt/local
ECE466LOC?=/users/sgaffer/Documents/ECE466
ANTLR=$(ANTLRLOC)/share/antlr-2.7.7/antlr.jar
JAVA=$(JAVALOC)/java
JAVAC=$(JAVALOC)/javac
JAR=$(JAVALOC)/jar
JAVADOC=$(JAVALOC)/javadoc

JFLAGS = -cp $(CLASSPATH):$(ECE466LOC)/cetus-1.3/lib/cetus.jar:$(ANTLRLOC)/share/antlr-2.7.7/antlr.jar:.

SOURCES = proj1.java LLVMCodeGenPass.java

all: $(SOURCES:.java=.class)

%.class : %.java
	$(JAVAC) $(JFLAGS) $<

test: all
	$(JAVA) $(JFLAGS) proj1 -verbosity=1 main.c

clean:
	rm -Rf *.class cetus_output *.ll *~
