include "wa.mm";
include "biantrur.mm";
include "bitr4i.mm";

theorem mpbiran(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume mpbiran.1: |- "ps";
  assume mpbiran.2: |- "( ph <-> ( ps /\\ ch ) )";





  do {
    wph;
    wps;
    wch;
    wa;
    wch;
    mpbiran.2;
    wps;
    wch;
    mpbiran.1;
    biantrur;
    bitr4i;
  };

  return |- "( ph <-> ch )";
}
