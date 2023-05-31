include "wex.mm";
include "wn.mm";
include "wal.mm";
include "df-ex.mm";
include "hbn1.mm";
include "hbxfrbi.mm";

theorem hbe1(wph: $wff$ ph, vx: $setvar$ x) {





  do {
    wph;
    vx;
    wex;
    wph;
    wn;
    #;
    vx;
    wal;
    wn;
    vx;
    wph;
    vx;
    df-ex;
    @0;
    vx;
    hbn1;
    hbxfrbi;
  };

  return $|-$ $( E. x ph -> A. x E. x ph )$;
}
