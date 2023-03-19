include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "cspr.mm"
include "cfv.mm"
include "crab.mm"
include "cpw.mm"
include "cvv.mm"
include "fvex.mm"
include "ssrab2.mm"
include "elpwi2.mm"
include "eqeltri.mm"

theorem sprsymrelfolem1
  let cQ: class Q
  let cR: class R
  let cV: class V
  let vq: setvar q
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x
  assume sprsymrelfo.q: |- Q = { q e. ( Pairs ` V ) | A. a e. V A. b e. V ( q = { a , b } -> a R b ) }

  disjoint V q
  disjoint k x
  assert |- Q e. ~P ( Pairs ` V )

  proof
    cQ
    vq
    cv
    va
    cv
    #
    vb
    cv
    #
    cpr
    wceq
    @0
    @1
    cR
    wbr
    wi
    vb
    cV
    wral
    va
    cV
    wral
    #
    vq
    cV
    cspr
    cfv
    #
    crab
    #
    @3
    cpw
    sprsymrelfo.q
    @4
    @3
    cvv
    cV
    cspr
    fvex
    @2
    vq
    @3
    ssrab2
    elpwi2
    eqeltri
end
