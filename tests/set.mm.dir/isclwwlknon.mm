include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cclwwlkn.mm"
include "co.mm"
include "cclwwlknon.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "clwwlknon.mm"
include "elrab2.mm"

theorem isclwwlknon
  let cG: class G
  let cN: class N
  let cW: class W
  let cX: class X
  let vw: setvar w


  assert |- ( W e. ( X ( ClWWalksNOn ` G ) N ) <-> ( W e. ( N ClWWalksN G ) /\ ( W ` 0 ) = X ) )

  proof
    cc0
    vw
    cv
    #
    cfv
    #
    cX
    wceq
    cc0
    cW
    cfv
    #
    cX
    wceq
    vw
    cW
    cN
    cG
    cclwwlkn
    co
    cX
    cN
    cG
    cclwwlknon
    cfv
    co
    @0
    cW
    wceq
    @1
    @2
    cX
    cc0
    @0
    cW
    fveq1
    eqeq1d
    vw
    cG
    cN
    cX
    clwwlknon
    elrab2
end
