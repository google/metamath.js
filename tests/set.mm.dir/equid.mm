include "weq.mm";
include "ax7v1.mm";
include "pm2.43i.mm";
include "ax6ev.mm";
include "exlimiiv.mm";

theorem equid(vx: setvar x) {



  let vy: setvar y;

  do {
    vy;
    vx;
    weq;
    #;
    vx;
    vx;
    weq;
    #;
    vy;
    @0;
    @1;
    vy;
    vx;
    vx;
    ax7v1;
    pm2.43i;
    vy;
    vx;
    ax6ev;
    exlimiiv;
  };

  return |- "x = x";
}
