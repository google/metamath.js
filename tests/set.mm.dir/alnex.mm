include "wex.mm";
include "wn.mm";
include "wal.mm";
include "df-ex.mm";
include "con2bii.mm";

theorem alnex(wph: $wff$ ph, vx: $setvar$ x) {





  do {
    wph;
    vx;
    wex;
    wph;
    wn;
    vx;
    wal;
    wph;
    vx;
    df-ex;
    con2bii;
  };

  return $|-$ $( A. x -. ph <-> -. E. x ph )$;
}
