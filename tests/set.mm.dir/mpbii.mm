include "a1i.mm";
include "mpbid.mm";

theorem mpbii(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume mpbii.min: |- "ps";
  assume mpbii.maj: |- "( ph -> ( ps <-> ch ) )";





  do {
    wph;
    wps;
    wch;
    wps;
    wph;
    mpbii.min;
    a1i;
    mpbii.maj;
    mpbid;
  };

  return |- "( ph -> ch )";
}
