include "bicomi.mm";
include "mtbi.mm";

theorem mtbir(wph: 'wff' ph, wps: 'wff' ps) {
  assume mtbir.1: |- "-. ps";
  assume mtbir.2: |- "( ph <-> ps )";





  do {
    wps;
    wph;
    mtbir.1;
    wph;
    wps;
    mtbir.2;
    bicomi;
    mtbi;
  };

  return '|-' "-. ph";
}
