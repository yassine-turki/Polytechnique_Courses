
LINK_TARGET = \
	client \
	server

OBJS = \
	client.o \
	server.o

REBUILDABLES = $(OBJS) $(LINK_TARGET)

all : $(LINK_TARGET)

clean: 
	rm -f $(REBUILDABLES)

#Server:

server : server.o
	cc -g3 -o  $@ $< -lpthread

#Client:


client : client.o
	cc -g3 -o  $@ $< 
	

%.o : %.c
	cc -g3 -Wall -o $@ -c $<

