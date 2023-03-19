include "cv.mm"
include "wcel.mm"
include "id.mm"
include "ssriv.mm"

theorem ssid
  let cA: class A
  let vx: setvar x


  assert |- A C_ A

  proof
    vx
    cA
    cA
    vx
    cv
    cA
    wcel
    id
    ssriv
end
