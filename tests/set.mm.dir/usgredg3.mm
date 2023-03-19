include "cusgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "cedg.mm"
include "cv.mm"
include "wne.mm"
include "cpr.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "crn.mm"
include "wfun.mm"
include "ciedg.mm"
include "usgrfun.mm"
include "funeqi.mm"
include "sylibr.mm"
include "fvelrn.mm"
include "sylan.mm"
include "edgval.mm"
include "a1i.mm"
include "eqcomi.mm"
include "rneqi.mm"
include "syl6eq.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "eqid.mm"
include "usgredg.mm"
include "syldan.mm"

theorem usgredg3
  let vx: setvar x
  let vy: setvar y
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  assume usgredg3.v: |- V = ( Vtx ` G )
  assume usgredg3.e: |- E = ( iEdg ` G )

  disjoint E x
  disjoint E y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint V x
  disjoint V y
  disjoint X x
  disjoint X y
  assert |- ( ( G e. USGraph /\ X e. dom E ) -> E. x e. V E. y e. V ( x =/= y /\ ( E ` X ) = { x , y } ) )

  proof
    cG
    cusgr
    wcel
    #
    cX
    cE
    cdm
    wcel
    #
    cX
    cE
    cfv
    #
    cG
    cedg
    cfv
    #
    wcel
    vx
    cv
    #
    vy
    cv
    #
    wne
    @2
    @4
    @5
    cpr
    wceq
    wa
    vy
    cV
    wrex
    vx
    cV
    wrex
    @0
    @1
    wa
    @2
    cE
    crn
    #
    @3
    @0
    cE
    wfun
    #
    @1
    @2
    @6
    wcel
    @0
    cG
    ciedg
    cfv
    #
    wfun
    @7
    cG
    usgrfun
    cE
    @8
    usgredg3.e
    funeqi
    sylibr
    cX
    cE
    fvelrn
    sylan
    @0
    @3
    @6
    wceq
    @1
    @0
    @3
    @8
    crn
    #
    @6
    @3
    @9
    wceq
    @0
    cG
    edgval
    a1i
    @8
    cE
    cE
    @8
    usgredg3.e
    eqcomi
    rneqi
    syl6eq
    adantr
    eleqtrrd
    @2
    @3
    cG
    cV
    vx
    vy
    usgredg3.v
    @3
    eqid
    usgredg
    syldan
end
