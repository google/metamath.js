include "wsb.mm";
include "weq.mm";
include "wi.mm";
include "wal.mm";
include "sb4v.mm";
include "sb2v.mm";
include "impbii.mm";

theorem sb6(wph: wff ph, vx: setvar x, vy: setvar y) {

  disjoint x y;



  do {
    wph;
    vx;
    vy;
    wsb;
    vx;
    vy;
    weq;
    wph;
    wi;
    vx;
    wal;
    wph;
    vx;
    vy;
    sb4v;
    wph;
    vx;
    vy;
    sb2v;
    impbii;
  };

  return |- "( [ y / x ] ph <-> A. x ( x = y -> ph ) )";
}
