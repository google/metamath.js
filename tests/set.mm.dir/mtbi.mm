include "biimpri.mm";
include "mto.mm";

theorem mtbi(wph: 'wff' ph, wps: 'wff' ps) {
  assume mtbi.1: |- "-. ph";
  assume mtbi.2: |- "( ph <-> ps )";





  do {
    wps;
    wph;
    mtbi.1;
    wph;
    wps;
    mtbi.2;
    biimpri;
    mto;
  };

  return '|-' "-. ps";
}
