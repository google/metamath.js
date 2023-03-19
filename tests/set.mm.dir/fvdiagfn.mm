include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cvv.mm"
include "cfv.mm"
include "wceq.mm"
include "simpr.mm"
include "snex.mm"
include "xpexg.mm"
include "mpan2.mm"
include "adantr.mm"
include "cv.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem fvdiagfn
  let vx: setvar x
  let cB: class B
  let cF: class F
  let cI: class I
  let cW: class W
  let cX: class X
  let cV: class V
  assume fdiagfn.f: |- F = ( x e. B |-> ( I X. { x } ) )

  disjoint B x
  disjoint I x
  disjoint W x
  disjoint X x
  disjoint V x
  assert |- ( ( I e. W /\ X e. B ) -> ( F ` X ) = ( I X. { X } ) )

  proof
    cI
    cW
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    @1
    cI
    cX
    csn
    #
    cxp
    #
    cvv
    wcel
    #
    cX
    cF
    cfv
    @3
    wceq
    @0
    @1
    simpr
    @0
    @4
    @1
    @0
    @2
    cvv
    wcel
    @4
    cX
    snex
    cI
    @2
    cW
    cvv
    xpexg
    mpan2
    adantr
    vx
    cX
    cI
    vx
    cv
    #
    csn
    #
    cxp
    @3
    cB
    cvv
    cF
    @5
    cX
    wceq
    @6
    @2
    cI
    @5
    cX
    sneq
    xpeq2d
    fdiagfn.f
    fvmptg
    syl2anc
end
