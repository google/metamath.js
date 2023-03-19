include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "wn.mm"
include "cdif.mm"
include "wi.mm"
include "disj3.mm"
include "eleq2.mm"
include "eldifn.mm"
include "syl6bi.mm"
include "sylbi.mm"
include "imp.mm"

theorem disjel
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A i^i B ) = (/) /\ C e. A ) -> -. C e. B )

  proof
    cA
    cB
    cin
    c0
    wceq
    #
    cC
    cA
    wcel
    #
    cC
    cB
    wcel
    wn
    #
    @0
    cA
    cA
    cB
    cdif
    #
    wceq
    #
    @1
    @2
    wi
    cA
    cB
    disj3
    @4
    @1
    cC
    @3
    wcel
    @2
    cA
    @3
    cC
    eleq2
    cC
    cA
    cB
    eldifn
    syl6bi
    sylbi
    imp
end
