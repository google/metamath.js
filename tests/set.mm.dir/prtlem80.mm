include "wcel.mm"
include "neldifsnd.mm"

theorem prtlem80
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. B -> -. A e. ( C \ { A } ) )

  proof
    cA
    cB
    wcel
    cA
    cC
    neldifsnd
end
