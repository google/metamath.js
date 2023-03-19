include "cun.mm"
include "wcel.mm"
include "wo.mm"
include "elun.mm"
include "biimpi.mm"
include "orcomd.mm"
include "orcanai.mm"

theorem elunnel2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ( B u. C ) /\ -. A e. C ) -> A e. B )

  proof
    cA
    cB
    cC
    cun
    wcel
    #
    cA
    cC
    wcel
    #
    cA
    cB
    wcel
    #
    @0
    @2
    @1
    @0
    @2
    @1
    wo
    cA
    cB
    cC
    elun
    biimpi
    orcomd
    orcanai
end
