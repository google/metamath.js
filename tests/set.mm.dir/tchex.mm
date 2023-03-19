include "csqrt.mm"
include "crn.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cmpt.mm"
include "wf.mm"
include "cvv.mm"
include "wcel.mm"
include "eqid.mm"
include "fvrn0.mm"
include "a1i.mm"
include "fmpti.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cc.mm"
include "cnex.mm"
include "wss.mm"
include "sqrtf.mm"
include "frn.mm"
include "ax-mp.mm"
include "ssexi.mm"
include "p0ex.mm"
include "unex.mm"
include "fex2.mm"
include "mp3an.mm"

theorem tchex
  let vx: setvar x
  let c.xi: class .,
  let cV: class V
  let cW: class W
  assume tchex.v: |- V = ( Base ` W )

  disjoint V x
  assert |- ( x e. V |-> ( sqrt ` ( x ., x ) ) ) e. _V

  proof
    cV
    csqrt
    crn
    #
    c0
    csn
    #
    cun
    #
    vx
    cV
    vx
    cv
    #
    @3
    c.xi
    co
    #
    csqrt
    cfv
    #
    cmpt
    #
    wf
    cV
    cvv
    wcel
    @2
    cvv
    wcel
    @6
    cvv
    wcel
    vx
    cV
    @2
    @5
    @6
    @6
    eqid
    @5
    @2
    wcel
    @3
    cV
    wcel
    csqrt
    @4
    fvrn0
    a1i
    fmpti
    cV
    cW
    cbs
    cfv
    cvv
    tchex.v
    cW
    cbs
    fvex
    eqeltri
    @0
    @1
    @0
    cc
    cnex
    cc
    cc
    csqrt
    wf
    @0
    cc
    wss
    sqrtf
    cc
    cc
    csqrt
    frn
    ax-mp
    ssexi
    p0ex
    unex
    cV
    @2
    @6
    cvv
    cvv
    fex2
    mp3an
end
