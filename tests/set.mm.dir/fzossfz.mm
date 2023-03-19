include "cfzo.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "elfzofz.mm"
include "ssriv.mm"

theorem fzossfz
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cM: class M
  let cN: class N


  assert |- ( A ..^ B ) C_ ( A ... B )

  proof
    vx
    cA
    cB
    cfzo
    co
    cA
    cB
    cfz
    co
    vx
    cv
    cA
    cB
    elfzofz
    ssriv
end
