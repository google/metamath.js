include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "wa.mm"
include "ccnv.mm"
include "dffun6.mm"
include "fun2cnv.mm"
include "anbi2i.mm"
include "bitr4i.mm"

theorem svrelfun
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( Fun A <-> ( Rel A /\ Fun `' `' A ) )

  proof
    cA
    wfun
    cA
    wrel
    #
    vx
    cv
    vy
    cv
    cA
    wbr
    vy
    wmo
    vx
    wal
    #
    wa
    @0
    cA
    ccnv
    ccnv
    wfun
    #
    wa
    vx
    vy
    cA
    dffun6
    @2
    @1
    @0
    vx
    vy
    cA
    fun2cnv
    anbi2i
    bitr4i
end
