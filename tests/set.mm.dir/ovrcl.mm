include "co.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "wa.mm"
include "n0i.mm"
include "ovprc.mm"
include "nsyl2.mm"

theorem ovrcl
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume ovprc1.1: |- Rel dom F


  assert |- ( C e. ( A F B ) -> ( A e. _V /\ B e. _V ) )

  proof
    cC
    cA
    cB
    cF
    co
    #
    wcel
    @0
    c0
    wceq
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    @0
    cC
    n0i
    cA
    cB
    cF
    ovprc1.1
    ovprc
    nsyl2
end
