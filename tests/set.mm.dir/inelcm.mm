include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "elin.mm"
include "ne0i.mm"
include "sylbir.mm"

theorem inelcm
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. B /\ A e. C ) -> ( B i^i C ) =/= (/) )

  proof
    cA
    cB
    wcel
    cA
    cC
    wcel
    wa
    cA
    cB
    cC
    cin
    #
    wcel
    @0
    c0
    wne
    cA
    cB
    cC
    elin
    @0
    cA
    ne0i
    sylbir
end
