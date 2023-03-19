include "cvv.mm"
include "wcel.mm"
include "crdg.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "wlim.mm"
include "cima.mm"
include "cuni.mm"
include "wral.mm"
include "wa.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "dfrdg2.mm"
include "iftrue.mm"
include "ifeq1d.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "unieqd.mm"
include "eqtr4d.mm"
include "wn.mm"
include "0ex.mm"
include "ax-mp.mm"
include "rdgprc.mm"
include "iffalse.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem dfrdg3
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cF: class F
  let cI: class I

  disjoint F f
  disjoint f x
  disjoint F x
  disjoint f y
  disjoint F y
  disjoint I f
  disjoint I x
  disjoint I y
  disjoint x y
  assert |- rec ( F , I ) = U. { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = if ( y = (/) , if ( I e. _V , I , (/) ) , if ( Lim y , U. ( f " y ) , ( F ` ( f ` U. y ) ) ) ) ) }

  proof
    cI
    cvv
    wcel
    #
    cF
    cI
    crdg
    #
    vf
    cv
    #
    vx
    cv
    #
    wfn
    #
    vy
    cv
    #
    @2
    cfv
    #
    @5
    c0
    wceq
    #
    @0
    cI
    c0
    cif
    #
    @5
    wlim
    @2
    @5
    cima
    cuni
    @5
    cuni
    @2
    cfv
    cF
    cfv
    cif
    #
    cif
    #
    wceq
    #
    vy
    @3
    wral
    #
    wa
    #
    vx
    con0
    wrex
    #
    vf
    cab
    #
    cuni
    #
    wceq
    @0
    @1
    @4
    @6
    @7
    cI
    @9
    cif
    #
    wceq
    #
    vy
    @3
    wral
    #
    wa
    #
    vx
    con0
    wrex
    #
    vf
    cab
    #
    cuni
    @16
    vx
    vy
    vf
    cF
    cI
    cvv
    dfrdg2
    @0
    @15
    @22
    @0
    @14
    @21
    vf
    @0
    @13
    @20
    vx
    con0
    @0
    @12
    @19
    @4
    @0
    @11
    @18
    vy
    @3
    @0
    @10
    @17
    @6
    @0
    @7
    @8
    cI
    @9
    @0
    cI
    c0
    iftrue
    ifeq1d
    eqeq2d
    ralbidv
    anbi2d
    rexbidv
    abbidv
    unieqd
    eqtr4d
    @0
    wn
    #
    cF
    c0
    crdg
    #
    @4
    @6
    @7
    c0
    @9
    cif
    #
    wceq
    #
    vy
    @3
    wral
    #
    wa
    #
    vx
    con0
    wrex
    #
    vf
    cab
    #
    cuni
    #
    @1
    @16
    c0
    cvv
    wcel
    @24
    @31
    wceq
    0ex
    vx
    vy
    vf
    cF
    c0
    cvv
    dfrdg2
    ax-mp
    cF
    cI
    rdgprc
    @23
    @15
    @30
    @23
    @14
    @29
    vf
    @23
    @13
    @28
    vx
    con0
    @23
    @12
    @27
    @4
    @23
    @11
    @26
    vy
    @3
    @23
    @10
    @25
    @6
    @23
    @7
    @8
    c0
    @9
    @0
    cI
    c0
    iffalse
    ifeq1d
    eqeq2d
    ralbidv
    anbi2d
    rexbidv
    abbidv
    unieqd
    3eqtr4a
    pm2.61i
end
