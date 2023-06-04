include "wa.mm";
include "wb.mm";
include "ibar.mm";
include "ax-mp.mm";

theorem biantrur(wph: 'wff' ph, wps: 'wff' ps) {
  assume biantrur.1: |- "ph";





  do {
    wph;
    wps;
    wph;
    wps;
    wa;
    wb;
    biantrur.1;
    wph;
    wps;
    ibar;
    ax-mp;
  };

  return '|-' "( ps <-> ( ph /\\ ps ) )";
}
