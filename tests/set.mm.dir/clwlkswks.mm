include "cclwlks.mm"
include "cfv.mm"
include "cwlks.mm"
include "cv.mm"
include "clwlkwlk.mm"
include "ssriv.mm"

theorem clwlkswks
  let cG: class G
  let vw: setvar w


  assert |- ( ClWalks ` G ) C_ ( Walks ` G )

  proof
    vw
    cG
    cclwlks
    cfv
    cG
    cwlks
    cfv
    cG
    vw
    cv
    clwlkwlk
    ssriv
end
