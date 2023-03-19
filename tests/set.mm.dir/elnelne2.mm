include "wnel.mm"
include "wcel.mm"
include "wn.mm"
include "wne.mm"
include "df-nel.mm"
include "nelne2.mm"
include "sylan2b.mm"

theorem elnelne2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. C /\ B e/ C ) -> A =/= B )

  proof
    cB
    cC
    wnel
    cA
    cC
    wcel
    cB
    cC
    wcel
    wn
    cA
    cB
    wne
    cB
    cC
    df-nel
    cA
    cB
    cC
    nelne2
    sylan2b
end
