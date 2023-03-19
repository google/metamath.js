include "cwwspthsn.mm"
include "co.mm"
include "cwwlksn.mm"
include "cv.mm"
include "wcel.mm"
include "cn0.mm"
include "cvv.mm"
include "wa.mm"
include "cspths.mm"
include "cfv.mm"
include "wbr.mm"
include "wex.mm"
include "wspthnp.mm"
include "simp2d.mm"
include "ssriv.mm"

theorem wspthsswwlkn
  let cG: class G
  let cN: class N
  let vf: setvar f
  let vw: setvar w


  assert |- ( N WSPathsN G ) C_ ( N WWalksN G )

  proof
    vw
    cN
    cG
    cwwspthsn
    co
    #
    cN
    cG
    cwwlksn
    co
    #
    vw
    cv
    #
    @0
    wcel
    cN
    cn0
    wcel
    cG
    cvv
    wcel
    wa
    @2
    @1
    wcel
    vf
    cv
    @2
    cG
    cspths
    cfv
    wbr
    vf
    wex
    vf
    cG
    cN
    @2
    wspthnp
    simp2d
    ssriv
end
