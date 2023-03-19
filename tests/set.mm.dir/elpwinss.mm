include "cpw.mm"
include "cin.mm"
include "wcel.mm"
include "elinel1.mm"
include "elpwid.mm"

theorem elpwinss
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( ~P B i^i C ) -> A C_ B )

  proof
    cA
    cB
    cpw
    #
    cC
    cin
    wcel
    cA
    cB
    cA
    @0
    cC
    elinel1
    elpwid
end
