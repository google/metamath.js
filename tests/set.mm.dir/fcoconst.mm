include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "ccom.mm"
include "cfv.mm"
include "cmpt.mm"
include "cv.mm"
include "simplr.mm"
include "wceq.mm"
include "fconstmpt.mm"
include "a1i.mm"
include "cvv.mm"
include "wf.mm"
include "simpl.mm"
include "dffn2.mm"
include "sylib.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "syl6eqr.mm"

theorem fcoconst
  let cF: class F
  let cI: class I
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F Fn X /\ Y e. X ) -> ( F o. ( I X. { Y } ) ) = ( I X. { ( F ` Y ) } ) )

  proof
    cF
    cX
    wfn
    #
    cY
    cX
    wcel
    #
    wa
    #
    cF
    cI
    cY
    csn
    cxp
    #
    ccom
    vx
    cI
    cY
    cF
    cfv
    #
    cmpt
    cI
    @4
    csn
    cxp
    @2
    vx
    vy
    cI
    cX
    cY
    vy
    cv
    #
    cF
    cfv
    @4
    @3
    cF
    @0
    @1
    vx
    cv
    cI
    wcel
    simplr
    @3
    vx
    cI
    cY
    cmpt
    wceq
    @2
    vx
    cI
    cY
    fconstmpt
    a1i
    @2
    vy
    cX
    cvv
    cF
    @2
    @0
    cX
    cvv
    cF
    wf
    @0
    @1
    simpl
    cX
    cF
    dffn2
    sylib
    feqmptd
    @5
    cY
    cF
    fveq2
    fmptco
    vx
    cI
    @4
    fconstmpt
    syl6eqr
end
