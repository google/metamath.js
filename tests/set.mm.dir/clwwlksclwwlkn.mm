include "cclwwlkn.mm"
include "co.mm"
include "cclwwlk.mm"
include "cfv.mm"
include "cv.mm"
include "clwwlkclwwlkn.mm"
include "ssriv.mm"

theorem clwwlksclwwlkn
  let cG: class G
  let cN: class N
  let vw: setvar w


  assert |- ( N ClWWalksN G ) C_ ( ClWWalks ` G )

  proof
    vw
    cN
    cG
    cclwwlkn
    co
    cG
    cclwwlk
    cfv
    cG
    cN
    vw
    cv
    clwwlkclwwlkn
    ssriv
end
