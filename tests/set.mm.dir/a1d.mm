include "wi.mm";
include "ax-1.mm";
include "syl.mm";

theorem a1d(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume a1d.1: |- "( ph -> ps )";





  do {
    wph;
    wps;
    wch;
    wps;
    wi;
    a1d.1;
    wps;
    wch;
    ax-1;
    syl;
  };

  return '|-' "( ph -> ( ch -> ps ) )";
}
