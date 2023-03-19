include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "wceq.mm"
include "negcon1.mm"
include "eqcom.mm"
include "syl6rbbr.mm"
include "syl6bb.mm"

theorem negcon2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A = -u B <-> B = -u A ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    wa
    #
    cA
    cB
    cneg
    #
    wceq
    #
    cA
    cneg
    #
    cB
    wceq
    #
    cB
    @3
    wceq
    @0
    @4
    @1
    cA
    wceq
    @2
    cA
    cB
    negcon1
    cA
    @1
    eqcom
    syl6rbbr
    @3
    cB
    eqcom
    syl6bb
end
