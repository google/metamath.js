include "wa.mm";
include "wb.mm";
include "iba.mm";
include "ax-mp.mm";

theorem biantru(wph: 'wff' ph, wps: 'wff' ps) {
  assume biantru.1: |- "ph";





  do {
    wph;
    wps;
    wps;
    wph;
    wa;
    wb;
    biantru.1;
    wph;
    wps;
    iba;
    ax-mp;
  };

  return '|-' "( ps <-> ( ps /\\ ph ) )";
}
