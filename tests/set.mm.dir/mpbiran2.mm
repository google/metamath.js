include "wa.mm";
include "biantru.mm";
include "bitr4i.mm";

theorem mpbiran2(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume mpbiran2.1: |- "ch";
  assume mpbiran2.2: |- "( ph <-> ( ps /\\ ch ) )";





  do {
    wph;
    wps;
    wch;
    wa;
    wps;
    mpbiran2.2;
    wch;
    wps;
    mpbiran2.1;
    biantru;
    bitr4i;
  };

  return |- "( ph <-> ps )";
}
