include "wnel.mm"
include "wcel.mm"
include "wn.mm"
include "wne.mm"
include "df-nel.mm"
include "nelne1.mm"
include "sylan2b.mm"

theorem elnelne1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. B /\ A e/ C ) -> B =/= C )

  proof
    cA
    cC
    wnel
    cA
    cB
    wcel
    cA
    cC
    wcel
    wn
    cB
    cC
    wne
    cA
    cC
    df-nel
    cA
    cB
    cC
    nelne1
    sylan2b
end
