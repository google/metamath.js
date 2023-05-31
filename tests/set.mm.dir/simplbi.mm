include "wa.mm";
include "biimpi.mm";
include "simpld.mm";

theorem simplbi(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {
  assume simplbi.1: $|- ( ph <-> ( ps /\ ch ) )$;





  do {
    wph;
    wps;
    wch;
    wph;
    wps;
    wch;
    wa;
    simplbi.1;
    biimpi;
    simpld;
  };

  return $|-$ $( ph -> ps )$;
}
