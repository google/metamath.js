include "weq.mm";
include "wal.mm";
include "wn.mm";
include "wex.mm";
include "wnf.mm";
include "exnal.mm";
include "hbe1.mm";
include "ax13lem2.mm";
include "ax13lem1.mm";
include "syldc.mm";
include "eximdh.mm";
include "hbe1a.mm";
include "syl6com.mm";
include "nfd.mm";
include "sylbir.mm";

theorem nfeqf2(vx: $setvar$ x, vy: $setvar$ y, vz: $setvar$ z) {

  disjoint x z;



  do {
    vx;
    vy;
    weq;
    #;
    vx;
    wal;
    wn;
    @0;
    wn;
    #;
    vx;
    wex;
    #;
    vz;
    vy;
    weq;
    #;
    vx;
    wnf;
    @0;
    vx;
    exnal;
    @2;
    @3;
    vx;
    @3;
    vx;
    wex;
    #;
    @2;
    @3;
    vx;
    wal;
    #;
    vx;
    wex;
    @5;
    @4;
    @1;
    @5;
    vx;
    @3;
    vx;
    hbe1;
    @1;
    @4;
    @3;
    @5;
    vx;
    vy;
    vz;
    ax13lem2;
    vx;
    vy;
    vz;
    ax13lem1;
    syldc;
    eximdh;
    @3;
    vx;
    hbe1a;
    syl6com;
    nfd;
    sylbir;
  };

  return $|-$ $( -. A. x x = y -> F/ x z = y )$;
}
