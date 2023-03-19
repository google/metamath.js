include "cin.mm"
include "wcel.mm"
include "elinel1.mm"
include "con3i.mm"

theorem nel1nelin
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( -. A e. B -> -. A e. ( B i^i C ) )

  proof
    cA
    cB
    cC
    cin
    wcel
    cA
    cB
    wcel
    cA
    cB
    cC
    elinel1
    con3i
end
