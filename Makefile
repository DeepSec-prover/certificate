FSTAR_LIB = FStar.Set.fst FStar.List.Tot.fst

FILES = term.fst
FILES_INTERFACE = term_interface.fst subst_interface.fst

all:
	fstar.exe $(FSTAR_LIB) $(FILES)

interface:
	fstar.exe $(FSTAR_LIB) $(FILES_INTERFACE)
