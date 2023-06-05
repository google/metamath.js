include "biimpri.mm";
include "syl.mm";

theorem sylbir(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume sylbir.1: |- "( ps <-> ph )";
  assume sylbir.2: |- "( ps -> ch )";





  do {
    wph;
    wps;
    wch;
    wps;
    wph;
    sylbir.1;
    biimpri;
    sylbir.2;
    syl;
  };

  return |- "( ph -> ch )";
}
