include "cpw.mm"
include "wcel.mm"
include "elpwi.mm"
include "sseld.mm"
include "impcom.mm"

theorem elelpwi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. B /\ B e. ~P C ) -> A e. C )

  proof
    cB
    cC
    cpw
    wcel
    #
    cA
    cB
    wcel
    cA
    cC
    wcel
    @0
    cB
    cC
    cA
    cB
    cC
    elpwi
    sseld
    impcom
end
