include "wb.mm";
include "wi.mm";
include "biimp.mm";
include "ax-mp.mm";

theorem biimpi(wph: 'wff' ph, wps: 'wff' ps) {
  assume biimpi.1: |- "( ph <-> ps )";





  do {
    wph;
    wps;
    wb;
    wph;
    wps;
    wi;
    biimpi.1;
    wph;
    wps;
    biimp;
    ax-mp;
  };

  return '|-' "( ph -> ps )";
}
