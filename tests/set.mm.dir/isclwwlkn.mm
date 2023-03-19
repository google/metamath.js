include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cclwwlk.mm"
include "cclwwlkn.mm"
include "co.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "clwwlkn.mm"
include "elrab2.mm"

theorem isclwwlkn
  let cG: class G
  let cN: class N
  let cW: class W
  let vw: setvar w


  assert |- ( W e. ( N ClWWalksN G ) <-> ( W e. ( ClWWalks ` G ) /\ ( # ` W ) = N ) )

  proof
    vw
    cv
    #
    chash
    cfv
    #
    cN
    wceq
    cW
    chash
    cfv
    #
    cN
    wceq
    vw
    cW
    cG
    cclwwlk
    cfv
    cN
    cG
    cclwwlkn
    co
    @0
    cW
    wceq
    @1
    @2
    cN
    @0
    cW
    chash
    fveq2
    eqeq1d
    vw
    cG
    cN
    clwwlkn
    elrab2
end
