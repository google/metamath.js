include "cchr.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "cur.mm"
include "cod.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq12d.mm"
include "df-chr.mm"
include "fvex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "0fv.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtr2i.mm"

theorem chrval
  let cC: class C
  let cR: class R
  let c.1: class .1.
  let cO: class O
  let vr: setvar r
  assume chrval.o: |- O = ( od ` R )
  assume chrval.u: |- .1. = ( 1r ` R )
  assume chrval.c: |- C = ( chr ` R )


  assert |- ( O ` .1. ) = C

  proof
    cC
    cR
    cchr
    cfv
    #
    c.1
    cO
    cfv
    #
    chrval.c
    cR
    cvv
    wcel
    #
    @0
    @1
    wceq
    vr
    cR
    vr
    cv
    #
    cur
    cfv
    #
    @3
    cod
    cfv
    #
    cfv
    @1
    cvv
    cchr
    @3
    cR
    wceq
    #
    @4
    c.1
    @5
    cO
    @6
    @5
    cR
    cod
    cfv
    #
    cO
    @3
    cR
    cod
    fveq2
    chrval.o
    syl6eqr
    @6
    @4
    cR
    cur
    cfv
    c.1
    @3
    cR
    cur
    fveq2
    chrval.u
    syl6eqr
    fveq12d
    vr
    df-chr
    c.1
    cO
    fvex
    fvmpt
    @2
    wn
    #
    @0
    c0
    @1
    cR
    cchr
    fvprc
    @8
    @1
    c.1
    c0
    cfv
    c0
    @8
    c.1
    cO
    c0
    @8
    cO
    @7
    c0
    chrval.o
    cR
    cod
    fvprc
    syl5eq
    fveq1d
    c.1
    0fv
    syl6eq
    eqtr4d
    pm2.61i
    eqtr2i
end
