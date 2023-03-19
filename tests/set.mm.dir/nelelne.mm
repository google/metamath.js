include "wcel.mm"
include "wn.mm"
include "wne.mm"
include "nelne2.mm"
include "expcom.mm"

theorem nelelne
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( -. A e. B -> ( C e. B -> C =/= A ) )

  proof
    cC
    cB
    wcel
    cA
    cB
    wcel
    wn
    cC
    cA
    wne
    cC
    cA
    cB
    nelne2
    expcom
end
