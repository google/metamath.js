include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wo.mm"
include "wceq.mm"
include "wn.mm"
include "sotrieq.mm"
include "bicomd.mm"
include "necon1abid.mm"

theorem sotrine
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R


  assert |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> ( B =/= C <-> ( B R C \/ C R B ) ) )

  proof
    cA
    cR
    wor
    cB
    cA
    wcel
    cC
    cA
    wcel
    wa
    wa
    #
    cB
    cC
    cR
    wbr
    cC
    cB
    cR
    wbr
    wo
    #
    cB
    cC
    @0
    cB
    cC
    wceq
    @1
    wn
    cA
    cB
    cC
    cR
    sotrieq
    bicomd
    necon1abid
end
