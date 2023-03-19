include "cdif.mm"
include "cv.mm"
include "eldifi.mm"
include "ssriv.mm"

theorem difss
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A \ B ) C_ A

  proof
    vx
    cA
    cB
    cdif
    cA
    vx
    cv
    cA
    cB
    eldifi
    ssriv
end
