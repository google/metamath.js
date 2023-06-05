include "weq.mm";
include "wsb.mm";
include "wi.mm";
include "wa.mm";
include "wex.mm";
include "id.mm";
include "ax6ev.mm";
include "ancli.mm";
include "eximii.mm";
include "df-sb.mm";
include "mpbir2an.mm";

theorem equsb1v(vx: setvar x, vy: setvar y) {

  disjoint x y;



  do {
    vx;
    vy;
    weq;
    #;
    vx;
    vy;
    wsb;
    @0;
    @0;
    wi;
    @0;
    @0;
    wa;
    #;
    vx;
    wex;
    @0;
    id;
    #;
    @0;
    @1;
    vx;
    vx;
    vy;
    ax6ev;
    @0;
    @0;
    @2;
    ancli;
    eximii;
    @0;
    vx;
    vy;
    df-sb;
    mpbir2an;
  };

  return |- "[ y / x ] x = y";
}
