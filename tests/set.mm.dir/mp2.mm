include "wi.mm";
include "ax-mp.mm";

theorem mp2(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume mp2.1: |- "ph";
  assume mp2.2: |- "ps";
  assume mp2.3: |- "( ph -> ( ps -> ch ) )";





  do {
    wps;
    wch;
    mp2.2;
    wph;
    wps;
    wch;
    wi;
    mp2.1;
    mp2.3;
    ax-mp;
    ax-mp;
  };

  return '|-' "ch";
}
