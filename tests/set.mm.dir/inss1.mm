include "cin.mm"
include "cv.mm"
include "elinel1.mm"
include "ssriv.mm"

theorem inss1
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A i^i B ) C_ A

  proof
    vx
    cA
    cB
    cin
    cA
    vx
    cv
    cA
    cB
    elinel1
    ssriv
end
