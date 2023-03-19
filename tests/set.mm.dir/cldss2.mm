include "ccld.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "cldss.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"

theorem cldss2
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  assume iscld.1: |- X = U. J


  assert |- ( Clsd ` J ) C_ ~P X

  proof
    vx
    cJ
    ccld
    cfv
    #
    cX
    cpw
    #
    vx
    cv
    #
    @0
    wcel
    @2
    cX
    wss
    @2
    @1
    wcel
    @2
    cJ
    cX
    iscld.1
    cldss
    vx
    cX
    selpw
    sylibr
    ssriv
end
