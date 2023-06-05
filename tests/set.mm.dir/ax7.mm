include "weq.mm";
include "wa.mm";
include "wi.mm";
include "ax7v2.mm";
include "ax7v1.mm";
include "imp.mm";
include "a1i.mm";
include "syl2and.mm";
include "ax6evr.mm";
include "exlimiiv.mm";
include "ex.mm";

theorem ax7(vx: setvar x, vy: setvar y, vz: setvar z) {



  let vt: setvar t;

  do {
    vx;
    vy;
    weq;
    #;
    vx;
    vz;
    weq;
    #;
    vy;
    vz;
    weq;
    #;
    vx;
    vt;
    weq;
    #;
    @0;
    @1;
    wa;
    @2;
    wi;
    vt;
    @3;
    @0;
    vt;
    vy;
    weq;
    #;
    @1;
    vt;
    vz;
    weq;
    #;
    @2;
    vx;
    vt;
    vy;
    ax7v2;
    vx;
    vt;
    vz;
    ax7v2;
    @4;
    @5;
    wa;
    @2;
    wi;
    @3;
    @4;
    @5;
    @2;
    vt;
    vy;
    vz;
    ax7v1;
    imp;
    a1i;
    syl2and;
    vt;
    vx;
    ax6evr;
    exlimiiv;
    ex;
  };

  return |- "( x = y -> ( x = z -> y = z ) )";
}
