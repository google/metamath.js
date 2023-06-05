include "wi.mm";
include "wsb.mm";
include "weq.mm";
include "wal.mm";
include "sb4v.mm";
include "ax-2.mm";
include "al2imi.mm";
include "sb2v.mm";
include "syl56.mm";
include "syl.mm";

theorem sbi1v(wph: wff ph, wps: wff ps, vx: setvar x, vy: setvar y) {

  disjoint x y;



  do {
    wph;
    wps;
    wi;
    #;
    vx;
    vy;
    wsb;
    vx;
    vy;
    weq;
    #;
    @0;
    wi;
    #;
    vx;
    wal;
    #;
    wph;
    vx;
    vy;
    wsb;
    #;
    wps;
    vx;
    vy;
    wsb;
    #;
    wi;
    @0;
    vx;
    vy;
    sb4v;
    @4;
    @1;
    wph;
    wi;
    #;
    vx;
    wal;
    @3;
    @1;
    wps;
    wi;
    #;
    vx;
    wal;
    @5;
    wph;
    vx;
    vy;
    sb4v;
    @2;
    @6;
    @7;
    vx;
    @1;
    wph;
    wps;
    ax-2;
    al2imi;
    wps;
    vx;
    vy;
    sb2v;
    syl56;
    syl;
  };

  return |- "( [ y / x ] ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) )";
}
