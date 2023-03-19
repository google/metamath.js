include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wbr.mm"
include "wo.mm"
include "wn.mm"
include "sotrieq.mm"
include "ioran.mm"
include "syl6bb.mm"

theorem sotrieq2
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R


  assert |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> ( B = C <-> ( -. B R C /\ -. C R B ) ) )

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
    cB
    cC
    wceq
    cB
    cC
    cR
    wbr
    #
    cC
    cB
    cR
    wbr
    #
    wo
    wn
    @0
    wn
    @1
    wn
    wa
    cA
    cB
    cC
    cR
    sotrieq
    @0
    @1
    ioran
    syl6bb
end
