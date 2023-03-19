include "cfv.mm"
include "crn.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cuni.mm"
include "wcel.mm"
include "wss.mm"
include "fvrn0.mm"
include "elssuni.mm"
include "ax-mp.mm"
include "uniun.mm"
include "0ex.mm"
include "unisn.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtri.mm"
include "sseqtri.mm"

theorem fvssunirn
  let cF: class F
  let cX: class X


  assert |- ( F ` X ) C_ U. ran F

  proof
    cX
    cF
    cfv
    #
    cF
    crn
    #
    c0
    csn
    #
    cun
    #
    cuni
    #
    @1
    cuni
    #
    @0
    @3
    wcel
    @0
    @4
    wss
    cF
    cX
    fvrn0
    @0
    @3
    elssuni
    ax-mp
    @4
    @5
    @2
    cuni
    #
    cun
    @5
    c0
    cun
    @5
    @1
    @2
    uniun
    @6
    c0
    @5
    c0
    0ex
    unisn
    uneq2i
    @5
    un0
    3eqtri
    sseqtri
end
