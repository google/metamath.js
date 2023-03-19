include "wcel.mm"
include "cv.mm"
include "casslaw.mm"
include "wbr.mm"
include "cclintop.mm"
include "cfv.mm"
include "crab.mm"
include "cvv.mm"
include "cassintop.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-assintop.mm"
include "a1i.mm"
include "fveq2.mm"
include "breq2.mm"
include "rabeqbidv.mm"
include "adantl.mm"
include "elex.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmptd.mm"

theorem assintopval
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
  assert |- ( M e. V -> ( assIntOp ` M ) = { o e. ( clIntOp ` M ) | o assLaw M } )

  proof
    cM
    cV
    wcel
    #
    vm
    cM
    vo
    cv
    #
    vm
    cv
    #
    casslaw
    wbr
    #
    vo
    @2
    cclintop
    cfv
    #
    crab
    #
    @1
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
    cvv
    cassintop
    cvv
    cassintop
    vm
    cvv
    @5
    cmpt
    wceq
    @0
    vm
    vo
    df-assintop
    a1i
    @2
    cM
    wceq
    #
    @5
    @8
    wceq
    @0
    @9
    @3
    @6
    vo
    @4
    @7
    @2
    cM
    cclintop
    fveq2
    @2
    cM
    @1
    casslaw
    breq2
    rabeqbidv
    adantl
    cM
    cV
    elex
    @8
    cvv
    wcel
    @0
    @6
    vo
    @7
    cM
    cclintop
    fvex
    rabex
    a1i
    fvmptd
end
