include "wa.mm";
include "anbi1i.mm";
include "anbi2i.mm";
include "bitri.mm";

theorem anbi12i(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume anbi12.1: |- "( ph <-> ps )";
  assume anbi12.2: |- "( ch <-> th )";





  do {
    wph;
    wch;
    wa;
    wps;
    wch;
    wa;
    wps;
    wth;
    wa;
    wph;
    wps;
    wch;
    anbi12.1;
    anbi1i;
    wch;
    wth;
    wps;
    anbi12.2;
    anbi2i;
    bitri;
  };

  return '|-' "( ( ph /\\ ch ) <-> ( ps /\\ th ) )";
}
