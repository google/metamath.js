include "impbid1.mm";
include "bicomd.mm";

theorem impbid2(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume impbid2.1: |- "( ps -> ch )";
  assume impbid2.2: |- "( ph -> ( ch -> ps ) )";





  do {
    wph;
    wch;
    wps;
    wph;
    wch;
    wps;
    impbid2.2;
    impbid2.1;
    impbid1;
    bicomd;
  };

  return '|-' "( ph -> ( ps <-> ch ) )";
}
