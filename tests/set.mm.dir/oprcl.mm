include "cop.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "wa.mm"
include "n0i.mm"
include "opprc.mm"
include "nsyl2.mm"

theorem oprcl
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( C e. <. A , B >. -> ( A e. _V /\ B e. _V ) )

  proof
    cC
    cA
    cB
    cop
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
    opprc
    nsyl2
end
