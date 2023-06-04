include "bicomd.mm";
include "bitrd.mm";

theorem bitr3d(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume bitr3d.1: |- "( ph -> ( ps <-> ch ) )";
  assume bitr3d.2: |- "( ph -> ( ps <-> th ) )";





  do {
    wph;
    wch;
    wps;
    wth;
    wph;
    wps;
    wch;
    bitr3d.1;
    bicomd;
    bitr3d.2;
    bitrd;
  };

  return '|-' "( ph -> ( ch <-> th ) )";
}
