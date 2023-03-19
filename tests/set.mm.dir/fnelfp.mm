include "wfn.mm"
include "cid.mm"
include "cin.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "fninfp.mm"
include "eleq2d.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "elrab3.mm"
include "sylan9bb.mm"

theorem fnelfp
  let cA: class A
  let cF: class F
  let cX: class X
  let vx: setvar x


  assert |- ( ( F Fn A /\ X e. A ) -> ( X e. dom ( F i^i _I ) <-> ( F ` X ) = X ) )

  proof
    cF
    cA
    wfn
    #
    cX
    cF
    cid
    cin
    cdm
    #
    wcel
    cX
    vx
    cv
    #
    cF
    cfv
    #
    @2
    wceq
    #
    vx
    cA
    crab
    #
    wcel
    cX
    cA
    wcel
    cX
    cF
    cfv
    #
    cX
    wceq
    #
    @0
    @1
    @5
    cX
    vx
    cA
    cF
    fninfp
    eleq2d
    @4
    @7
    vx
    cX
    cA
    @2
    cX
    wceq
    #
    @3
    @6
    @2
    cX
    @2
    cX
    cF
    fveq2
    @8
    id
    eqeq12d
    elrab3
    sylan9bb
end
