FSTAR_LIB = FStar.Set.fst FStar.List.Tot.fst

FILES = term.fst subst.fst
FILES_INTERFACE = term_interface.fst subst_interface.fst

all:
	fstar.exe $(FSTAR_LIB) $(FILES)

term:
	fstar.exe $(FSTAR_LIB) term.fst

interface:
	fstar.exe $(FSTAR_LIB) $(FILES_INTERFACE)

subst:
	fstar.exe $(FSTAR_LIB) subst.fst

mgu:
	fstar.exe mgu.fst
