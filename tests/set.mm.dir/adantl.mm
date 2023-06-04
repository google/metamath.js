include "adantr.mm";
include "ancoms.mm";

theorem adantl(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume adantl.1: |- "( ph -> ps )";





  do {
    wph;
    wch;
    wps;
    wph;
    wps;
    wch;
    adantl.1;
    adantr;
    ancoms;
  };

  return '|-' "( ( ch /\\ ph ) -> ps )";
}
