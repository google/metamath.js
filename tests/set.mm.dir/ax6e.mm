include "weq.mm";
include "wex.mm";
include "19.8a.mm";
include "wn.mm";
include "wi.mm";
include "wal.mm";
include "ax13lem1.mm";
include "ax6ev.mm";
include "equtr.mm";
include "eximii.mm";
include "19.35i.mm";
include "syl6com.mm";
include "exlimiiv.mm";
include "pm2.61i.mm";

theorem ax6e(vx: $setvar$ x, vy: $setvar$ y) {



  let vw: $setvar$ w;

  do {
    vx;
    vy;
    weq;
    #;
    @0;
    vx;
    wex;
    #;
    @0;
    vx;
    19.8a;
    vw;
    vy;
    weq;
    #;
    @0;
    wn;
    #;
    @1;
    wi;
    vw;
    @3;
    @2;
    @2;
    vx;
    wal;
    @1;
    vx;
    vy;
    vw;
    ax13lem1;
    @2;
    @0;
    vx;
    vx;
    vw;
    weq;
    @2;
    @0;
    wi;
    vx;
    vx;
    vw;
    ax6ev;
    vx;
    vw;
    vy;
    equtr;
    eximii;
    19.35i;
    syl6com;
    vw;
    vy;
    ax6ev;
    exlimiiv;
    pm2.61i;
  };

  return $|-$ $E. x x = y$;
}
