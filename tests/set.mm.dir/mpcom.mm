include "com12.mm";
include "mpd.mm";

theorem mpcom(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume mpcom.1: |- "( ps -> ph )";
  assume mpcom.2: |- "( ph -> ( ps -> ch ) )";





  do {
    wps;
    wph;
    wch;
    mpcom.1;
    wph;
    wps;
    wch;
    mpcom.2;
    com12;
    mpd;
  };

  return '|-' "( ps -> ch )";
}
