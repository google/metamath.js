include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "citg.mm"
include "fveq2.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "cbvitg.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "simpr.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "itgeq2dv.mm"
include "syl5req.mm"

theorem itgmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let vk: setvar k
  assume itgmpt.1: |- ( ( ph /\ x e. A ) -> B e. V )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint ph x
  disjoint V x
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint B k
  disjoint k ph
  assert |- ( ph -> S. A B _d x = S. A ( ( x e. A |-> B ) ` y ) _d y )

  proof
    wph
    vy
    cA
    vy
    cv
    #
    vx
    cA
    cB
    cmpt
    #
    cfv
    #
    citg
    vx
    cA
    vx
    cv
    #
    @1
    cfv
    #
    citg
    vx
    cA
    cB
    citg
    vy
    vx
    cA
    @2
    @4
    @0
    @3
    @1
    fveq2
    vx
    cA
    cB
    @0
    nffvmpt1
    vy
    @4
    nfcv
    cbvitg
    wph
    vx
    cA
    @4
    cB
    wph
    @3
    cA
    wcel
    #
    wa
    @5
    cB
    cV
    wcel
    @4
    cB
    wceq
    wph
    @5
    simpr
    itgmpt.1
    vx
    cA
    cB
    cV
    @1
    @1
    eqid
    fvmpt2
    syl2anc
    itgeq2dv
    syl5req
end
