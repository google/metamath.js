include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cint.mm"
include "cvv.mm"
include "ccf.mm"
include "cflem.mm"
include "intexab.mm"
include "sylib.mm"
include "sseq2.mm"
include "raleq.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "abbidv.mm"
include "inteqd.mm"
include "df-cf.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem cfval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let vv: setvar v

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint v w
  disjoint A v
  assert |- ( A e. On -> ( cf ` A ) = |^| { x | E. y ( x = ( card ` y ) /\ ( y C_ A /\ A. z e. A E. w e. y z C_ w ) ) } )

  proof
    cA
    con0
    wcel
    #
    vx
    cv
    vy
    cv
    #
    ccrd
    cfv
    wceq
    #
    @1
    cA
    wss
    #
    vz
    cv
    vw
    cv
    wss
    vw
    @1
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    cint
    #
    cvv
    wcel
    #
    cA
    ccf
    cfv
    @10
    wceq
    @0
    @8
    vx
    wex
    @11
    vx
    vy
    vz
    vw
    cA
    con0
    cflem
    @8
    vx
    intexab
    sylib
    vv
    cA
    @2
    @1
    vv
    cv
    #
    wss
    #
    @4
    vz
    @12
    wral
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    cint
    @10
    con0
    cvv
    ccf
    @12
    cA
    wceq
    #
    @18
    @9
    @19
    @17
    @8
    vx
    @19
    @16
    @7
    vy
    @19
    @15
    @6
    @2
    @19
    @13
    @3
    @14
    @5
    @12
    cA
    @1
    sseq2
    @4
    vz
    @12
    cA
    raleq
    anbi12d
    anbi2d
    exbidv
    abbidv
    inteqd
    vv
    vx
    vy
    vz
    vw
    df-cf
    fvmptg
    mpdan
end
