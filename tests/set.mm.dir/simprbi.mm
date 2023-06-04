include "wa.mm";
include "biimpi.mm";
include "simprd.mm";

theorem simprbi(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume simprbi.1: |- "( ph <-> ( ps /\\ ch ) )";





  do {
    wph;
    wps;
    wch;
    wph;
    wps;
    wch;
    wa;
    simprbi.1;
    biimpi;
    simprd;
  };

  return '|-' "( ph -> ch )";
}
