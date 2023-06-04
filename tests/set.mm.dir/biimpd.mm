include "wb.mm";
include "wi.mm";
include "biimp.mm";
include "syl.mm";

theorem biimpd(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume biimpd.1: |- "( ph -> ( ps <-> ch ) )";





  do {
    wph;
    wps;
    wch;
    wb;
    wps;
    wch;
    wi;
    biimpd.1;
    wps;
    wch;
    biimp;
    syl;
  };

  return '|-' "( ph -> ( ps -> ch ) )";
}
