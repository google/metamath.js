include "sbbid.mm";
include "abbilem.mm";

theorem abbid(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, vx: $setvar$ x) {
  assume abbid.1: $|- F/ x ph$;
  assume abbid.2: $|- ( ph -> ( ps <-> ch ) )$;



  let vy: $setvar$ y;

  do {
    wph;
    wps;
    wch;
    vx;
    vy;
    wph;
    wps;
    wch;
    vx;
    vy;
    abbid.1;
    abbid.2;
    sbbid;
    abbilem;
  };

  return $|-$ $( ph -> { x | ps } = { x | ch } )$;
}
