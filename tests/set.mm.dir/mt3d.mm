include "wn.mm";
include "con1d.mm";
include "mpd.mm";

theorem mt3d(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume mt3d.1: $|- ( ph -> -. ch )$;
  assume mt3d.2: $|- ( ph -> ( -. ps -> ch ) )$;





  do {
    wph;
    wch;
    wn;
    wps;
    mt3d.1;
    wph;
    wps;
    wch;
    mt3d.2;
    con1d;
    mpd;
  };

  return $|-$ $( ph -> ps )$;
}
