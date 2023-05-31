include "cv.mm";
include "wcel.mm";
include "wi.mm";
include "wa.mm";
include "cab.mm";
include "cif.mm";
include "dedlem0a.mm";
include "abbi2dv.mm";
include "dfif2.mm";
include "syl6reqr.mm";

theorem iftrue(wph: $wff$ ph, cA: $class$ A, cB: $class$ B) {



  let vx: $setvar$ x;
  let cC: $class$ C;

  do {
    wph;
    cA;
    vx;
    cv;
    #;
    cB;
    wcel;
    #;
    wph;
    wi;
    @0;
    cA;
    wcel;
    #;
    wph;
    wa;
    wi;
    #;
    vx;
    cab;
    wph;
    cA;
    cB;
    cif;
    wph;
    @3;
    vx;
    cA;
    wph;
    @2;
    @1;
    dedlem0a;
    abbi2dv;
    wph;
    vx;
    cA;
    cB;
    dfif2;
    syl6reqr;
  };

  return $|-$ $( ph -> if ( ph , A , B ) = A )$;
}
