include "weq.mm";
include "wa.mm";
include "wex.mm";
include "wn.mm";
include "wal.mm";
include "equvinva.mm";
include "ax13v.mm";
include "equeucl.mm";
include "alimdv.mm";
include "syl9.mm";
include "impd.mm";
include "exlimdv.mm";
include "syl5.mm";

theorem ax13lem1(vx: 'setvar' x, vy: 'setvar' y, vz: 'setvar' z) {

  disjoint x z;
  disjoint w x;
  disjoint w z;
  disjoint w y;

  let vw: setvar w;

  do {
    vz;
    vy;
    weq;
    #;
    vz;
    vw;
    weq;
    #;
    vy;
    vw;
    weq;
    #;
    wa;
    #;
    vw;
    wex;
    vx;
    vy;
    weq;
    wn;
    #;
    @0;
    vx;
    wal;
    #;
    vz;
    vy;
    vw;
    equvinva;
    @4;
    @3;
    @5;
    vw;
    @4;
    @1;
    @2;
    @5;
    @4;
    @2;
    @2;
    vx;
    wal;
    @1;
    @5;
    vx;
    vy;
    vw;
    ax13v;
    @1;
    @2;
    @0;
    vx;
    vz;
    vy;
    vw;
    equeucl;
    alimdv;
    syl9;
    impd;
    exlimdv;
    syl5;
  };

  return '|-' "( -. x = y -> ( z = y -> A. x z = y ) )";
}
