# Certify every example book, one at a time (examples/certify.sh holds a lock).
#   make            certify all
#   make clean      remove certification products
# Books are listed by their .lisp path; each must certify in well under a
# minute on the laptop, and only include community books the laptop has
# certified (see sources.md, "community books available").
BOOKS := $(shell find . -name '*.lisp' -not -path './.cert.lock/*' | sort)
CERTS := $(BOOKS:.lisp=.cert)

all: $(CERTS)

%.cert: %.lisp
	./certify.sh $<

clean:
	find . \( -name '*.cert' -o -name '*.cert.out' -o -name '*.cert.time' -o -name '*.fasl' -o -name '*.port' -o -name 'Makefile-tmp' \) -delete

.PHONY: all clean
