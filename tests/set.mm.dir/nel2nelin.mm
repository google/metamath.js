include "cin.mm"
include "wcel.mm"
include "elinel2.mm"
include "con3i.mm"

theorem nel2nelin
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( -. A e. C -> -. A e. ( B i^i C ) )

  proof
    cA
    cB
    cC
    cin
    wcel
    cA
    cC
    wcel
    cA
    cB
    cC
    elinel2
    con3i
end
