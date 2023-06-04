include "wi.mm";
include "ax-1.mm";
include "syl.mm";

theorem jarri(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume jarri.1: |- "( ( ph -> ps ) -> ch )";





  do {
    wps;
    wph;
    wps;
    wi;
    wch;
    wps;
    wph;
    ax-1;
    jarri.1;
    syl;
  };

  return '|-' "( ps -> ch )";
}
