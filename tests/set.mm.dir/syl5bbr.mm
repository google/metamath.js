include "bicomi.mm";
include "syl5bb.mm";

theorem syl5bbr(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume syl5bbr.1: |- "( ps <-> ph )";
  assume syl5bbr.2: |- "( ch -> ( ps <-> th ) )";





  do {
    wph;
    wps;
    wch;
    wth;
    wps;
    wph;
    syl5bbr.1;
    bicomi;
    syl5bbr.2;
    syl5bb;
  };

  return '|-' "( ch -> ( ph <-> th ) )";
}
