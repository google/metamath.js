include "id.mm";
include "orim12i.mm";

theorem orim2i(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume orim1i.1: |- "( ph -> ps )";





  do {
    wch;
    wch;
    wph;
    wps;
    wch;
    id;
    orim1i.1;
    orim12i;
  };

  return '|-' "( ( ch \\/ ph ) -> ( ch \\/ ps ) )";
}
