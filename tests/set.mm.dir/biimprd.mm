include "id.mm";
include "syl5ibr.mm";

theorem biimprd(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume biimprd.1: |- "( ph -> ( ps <-> ch ) )";





  do {
    wch;
    wps;
    wph;
    wch;
    wch;
    id;
    biimprd.1;
    syl5ibr;
  };

  return '|-' "( ph -> ( ch -> ps ) )";
}
