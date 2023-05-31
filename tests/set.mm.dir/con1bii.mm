include "wn.mm";
include "notnotb.mm";
include "xchbinx.mm";
include "bicomi.mm";

theorem con1bii(wph: $wff$ ph, wps: $wff$ ps) {
  assume con1bii.1: $|- ( -. ph <-> ps )$;





  do {
    wph;
    wps;
    wn;
    wph;
    wph;
    wn;
    wps;
    wph;
    notnotb;
    con1bii.1;
    xchbinx;
    bicomi;
  };

  return $|-$ $( -. ps <-> ph )$;
}
