include "wal.mm";
include "wn.mm";
include "wex.mm";
include "alex.mm";
include "con2bii.mm";

theorem exnal(wph: 'wff' ph, vx: 'setvar' x) {





  do {
    wph;
    vx;
    wal;
    wph;
    wn;
    vx;
    wex;
    wph;
    vx;
    alex;
    con2bii;
  };

  return '|-' "( E. x -. ph <-> -. A. x ph )";
}
