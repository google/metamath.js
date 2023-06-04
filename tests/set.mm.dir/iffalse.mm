include "wn.mm";
include "cv.mm";
include "wcel.mm";
include "wa.mm";
include "wo.mm";
include "cab.mm";
include "cif.mm";
include "dedlemb.mm";
include "abbi2dv.mm";
include "df-if.mm";
include "syl6reqr.mm";

theorem iffalse(wph: 'wff' ph, cA: 'class' A, cB: 'class' B) {



  let vx: setvar x;

  do {
    wph;
    wn;
    #;
    cB;
    vx;
    cv;
    #;
    cA;
    wcel;
    #;
    wph;
    wa;
    @1;
    cB;
    wcel;
    #;
    @0;
    wa;
    wo;
    #;
    vx;
    cab;
    wph;
    cA;
    cB;
    cif;
    @0;
    @4;
    vx;
    cB;
    wph;
    @2;
    @3;
    dedlemb;
    abbi2dv;
    wph;
    vx;
    cA;
    cB;
    df-if;
    syl6reqr;
  };

  return '|-' "( -. ph -> if ( ph , A , B ) = B )";
}
