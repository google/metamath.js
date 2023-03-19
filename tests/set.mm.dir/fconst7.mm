include "csn.mm"
include "wf.mm"
include "cxp.mm"
include "wceq.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cvv.mm"
include "fvexd.mm"
include "eqeltrrd.mm"
include "snidg.mm"
include "syl.mm"
include "eqeltrd.mm"
include "ralrimia.mm"
include "nfcv.mm"
include "ffnfvf.mm"
include "sylanbrc.mm"
include "wb.mm"
include "fconst2g.mm"
include "mpbid.mm"

theorem fconst7
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  assume fconst7.p: |- F/ x ph
  assume fconst7.x: |- F/_ x F
  assume fconst7.f: |- ( ph -> F Fn A )
  assume fconst7.b: |- ( ph -> B e. V )
  assume fconst7.e: |- ( ( ph /\ x e. A ) -> ( F ` x ) = B )

  disjoint A x
  disjoint B x
  assert |- ( ph -> F = ( A X. { B } ) )

  proof
    wph
    cA
    cB
    csn
    #
    cF
    wf
    #
    cF
    cA
    @0
    cxp
    wceq
    #
    wph
    cF
    cA
    wfn
    vx
    cv
    #
    cF
    cfv
    #
    @0
    wcel
    #
    vx
    cA
    wral
    @1
    fconst7.f
    wph
    @5
    vx
    cA
    fconst7.p
    wph
    @3
    cA
    wcel
    wa
    #
    @4
    cB
    @0
    fconst7.e
    @6
    cB
    cvv
    wcel
    cB
    @0
    wcel
    @6
    @4
    cB
    cvv
    fconst7.e
    @6
    @3
    cF
    fvexd
    eqeltrrd
    cB
    cvv
    snidg
    syl
    eqeltrd
    ralrimia
    vx
    cA
    @0
    cF
    vx
    cA
    nfcv
    vx
    @0
    nfcv
    fconst7.x
    ffnfvf
    sylanbrc
    wph
    cB
    cV
    wcel
    @1
    @2
    wb
    fconst7.b
    cA
    cB
    cV
    cF
    fconst2g
    syl
    mpbid
end
