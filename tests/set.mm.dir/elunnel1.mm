include "cun.mm"
include "wcel.mm"
include "wo.mm"
include "elun.mm"
include "biimpi.mm"
include "orcanai.mm"

theorem elunnel1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ( B u. C ) /\ -. A e. B ) -> A e. C )

  proof
    cA
    cB
    cC
    cun
    wcel
    #
    cA
    cB
    wcel
    #
    cA
    cC
    wcel
    #
    @0
    @1
    @2
    wo
    cA
    cB
    cC
    elun
    biimpi
    orcanai
end
