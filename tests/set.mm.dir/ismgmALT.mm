include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "ccllaw.mm"
include "wbr.mm"
include "cmgm2.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breq12d.mm"
include "df-mgm2.mm"
include "elab2g.mm"

theorem ismgmALT
  let cB: class B
  let cM: class M
  let cV: class V
  let c.op: class .o.
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x
  assume ismgmALT.b: |- B = ( Base ` M )
  assume ismgmALT.o: |- .o. = ( +g ` M )


  assert |- ( M e. V -> ( M e. MgmALT <-> .o. clLaw B ) )

  proof
    vm
    cv
    #
    cplusg
    cfv
    #
    @0
    cbs
    cfv
    #
    ccllaw
    wbr
    c.op
    cB
    ccllaw
    wbr
    vm
    cM
    cmgm2
    cV
    @0
    cM
    wceq
    #
    @1
    c.op
    @2
    cB
    ccllaw
    @3
    @1
    cM
    cplusg
    cfv
    c.op
    @0
    cM
    cplusg
    fveq2
    ismgmALT.o
    syl6eqr
    @3
    @2
    cM
    cbs
    cfv
    cB
    @0
    cM
    cbs
    fveq2
    ismgmALT.b
    syl6eqr
    breq12d
    vm
    df-mgm2
    elab2g
end
