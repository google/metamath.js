include "codd.mm"
include "wcel.mm"
include "ceven.mm"
include "wn.mm"
include "wne.mm"
include "oddneven.mm"
include "nelne2.mm"
include "sylan2.mm"

theorem zneoALTV
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. Even /\ B e. Odd ) -> A =/= B )

  proof
    cB
    codd
    wcel
    cA
    ceven
    wcel
    cB
    ceven
    wcel
    wn
    cA
    cB
    wne
    cB
    oddneven
    cA
    cB
    ceven
    nelne2
    sylan2
end
