include "biimpd.mm";
include "mpd.mm";

theorem mpbid(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume mpbid.min: $|- ( ph -> ps )$;
  assume mpbid.maj: $|- ( ph -> ( ps <-> ch ) )$;





  do {
    wph;
    wps;
    wch;
    mpbid.min;
    wph;
    wps;
    wch;
    mpbid.maj;
    biimpd;
    mpd;
  };

  return $|-$ $( ph -> ch )$;
}
