include "wi.mm";
include "ax-1.mm";
include "ax-mp.mm";

theorem a1i(wph: 'wff' ph, wps: 'wff' ps) {
  assume a1i.1: |- "ph";





  do {
    wph;
    wps;
    wph;
    wi;
    a1i.1;
    wph;
    wps;
    ax-1;
    ax-mp;
  };

  return '|-' "( ps -> ph )";
}
