include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmpt.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"

theorem fvmpt4
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  assert |- ( ( x e. A /\ B e. C ) -> ( ( x e. A |-> B ) ` x ) = B )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    cB
    cC
    wcel
    #
    wa
    @1
    @2
    @0
    vx
    cA
    cB
    cmpt
    #
    cfv
    cB
    wceq
    @1
    @2
    simpl
    @1
    @2
    simpr
    vx
    cA
    cB
    cC
    @3
    @3
    eqid
    fvmpt2
    syl2anc
end
