include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "cuni.mm"
include "wceq.mm"
include "elssuni.mm"
include "unissb.mm"
include "biimpri.mm"
include "anim12i.mm"
include "eqss.mm"
include "sylibr.mm"

theorem ssunieq
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. B /\ A. x e. B x C_ A ) -> A = U. B )

  proof
    cA
    cB
    wcel
    #
    vx
    cv
    cA
    wss
    vx
    cB
    wral
    #
    wa
    cA
    cB
    cuni
    #
    wss
    #
    @2
    cA
    wss
    #
    wa
    cA
    @2
    wceq
    @0
    @3
    @1
    @4
    cA
    cB
    elssuni
    @4
    @1
    vx
    cB
    cA
    unissb
    biimpri
    anim12i
    cA
    @2
    eqss
    sylibr
end
