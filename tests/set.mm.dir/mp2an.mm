include "mpan.mm";
include "ax-mp.mm";

theorem mp2an(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume mp2an.1: |- "ph";
  assume mp2an.2: |- "ps";
  assume mp2an.3: |- "( ( ph /\\ ps ) -> ch )";





  do {
    wps;
    wch;
    mp2an.2;
    wph;
    wps;
    wch;
    mp2an.1;
    mp2an.3;
    mpan;
    ax-mp;
  };

  return '|-' "ch";
}
