include "cwwlksn.mm"
include "co.mm"
include "cwwlks.mm"
include "cfv.mm"
include "cv.mm"
include "wwlkswwlksn.mm"
include "ssriv.mm"

theorem wwlkssswwlksn
  let cG: class G
  let cN: class N
  let vw: setvar w


  assert |- ( N WWalksN G ) C_ ( WWalks ` G )

  proof
    vw
    cN
    cG
    cwwlksn
    co
    cG
    cwwlks
    cfv
    cG
    cN
    vw
    cv
    wwlkswwlksn
    ssriv
end
