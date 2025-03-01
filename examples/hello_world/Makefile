.POSIX:
.SUFFIXES: .olea .asm

OLEAC := ../../target/debug/olea

ASM = main.asm
SOURCE = $(OBJECTS:.o=.olea)

main.img: main.fxf
	$(RYFS) create $@
	$(RYFS) add $@ $<

main.fxf: entry.asm $(ASM)
	$(FOX32ASM) $< $@

.olea.asm:
	$(OLEAC) $< > $@
	cat $@
