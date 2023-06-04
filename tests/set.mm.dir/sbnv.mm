include "weq.mm";
include "wn.mm";
include "wa.mm";
include "wex.mm";
include "wi.mm";
include "wal.mm";
include "wsb.mm";
include "exanali.mm";
include "sb5.mm";
include "sb6.mm";
include "notbii.mm";
include "3bitr4i.mm";

theorem sbnv(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {

  disjoint x y;



  do {
    vx;
    vy;
    weq;
    #;
    wph;
    wn;
    #;
    wa;
    vx;
    wex;
    @0;
    wph;
    wi;
    vx;
    wal;
    #;
    wn;
    @1;
    vx;
    vy;
    wsb;
    wph;
    vx;
    vy;
    wsb;
    #;
    wn;
    @0;
    wph;
    vx;
    exanali;
    @1;
    vx;
    vy;
    sb5;
    @3;
    @2;
    wph;
    vx;
    vy;
    sb6;
    notbii;
    3bitr4i;
  };

  return '|-' "( [ y / x ] -. ph <-> -. [ y / x ] ph )";
}
