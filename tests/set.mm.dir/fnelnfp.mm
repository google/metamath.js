include "wfn.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "crab.mm"
include "fndifnfp.mm"
include "eleq2d.mm"
include "wceq.mm"
include "fveq2.mm"
include "id.mm"
include "neeq12d.mm"
include "elrab3.mm"
include "sylan9bb.mm"

theorem fnelnfp
  let cA: class A
  let cF: class F
  let cX: class X
  let vx: setvar x


  assert |- ( ( F Fn A /\ X e. A ) -> ( X e. dom ( F \ _I ) <-> ( F ` X ) =/= X ) )

  proof
    cF
    cA
    wfn
    #
    cX
    cF
    cid
    cdif
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
    wne
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
    wne
    #
    @0
    @1
    @5
    cX
    vx
    cA
    cF
    fndifnfp
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
    neeq12d
    elrab3
    sylan9bb
end
