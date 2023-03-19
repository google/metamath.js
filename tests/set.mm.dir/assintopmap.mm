include "wcel.mm"
include "cassintop.mm"
include "cfv.mm"
include "cv.mm"
include "casslaw.mm"
include "wbr.mm"
include "cclintop.mm"
include "crab.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "assintopval.mm"
include "wceq.mm"
include "clintopval.mm"
include "rabeq.mm"
include "syl.mm"
include "eqtrd.mm"

theorem assintopmap
  let vo: setvar o
  let cM: class M
  let cV: class V
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x

  disjoint M o
  disjoint M m
  disjoint V m
  disjoint m o
  disjoint k x
  assert |- ( M e. V -> ( assIntOp ` M ) = { o e. ( M ^m ( M X. M ) ) | o assLaw M } )

  proof
    cM
    cV
    wcel
    #
    cM
    cassintop
    cfv
    vo
    cv
    cM
    casslaw
    wbr
    #
    vo
    cM
    cclintop
    cfv
    #
    crab
    #
    @1
    vo
    cM
    cM
    cM
    cxp
    cmap
    co
    #
    crab
    #
    vo
    cM
    cV
    assintopval
    @0
    @2
    @4
    wceq
    @3
    @5
    wceq
    cM
    cV
    clintopval
    @1
    vo
    @2
    @4
    rabeq
    syl
    eqtrd
end
