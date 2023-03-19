include "cfz.mm"
include "co.mm"
include "cz.mm"
include "cv.mm"
include "elfzelz.mm"
include "ssriv.mm"

theorem fzssz
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( M ... N ) C_ ZZ

  proof
    vx
    cM
    cN
    cfz
    co
    cz
    vx
    cv
    cM
    cN
    elfzelz
    ssriv
end
