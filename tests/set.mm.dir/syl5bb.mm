include "wb.mm";
include "a1i.mm";
include "bitrd.mm";

theorem syl5bb(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume syl5bb.1: |- "( ph <-> ps )";
  assume syl5bb.2: |- "( ch -> ( ps <-> th ) )";





  do {
    wch;
    wph;
    wps;
    wth;
    wph;
    wps;
    wb;
    wch;
    syl5bb.1;
    a1i;
    syl5bb.2;
    bitrd;
  };

  return '|-' "( ch -> ( ph <-> th ) )";
}
