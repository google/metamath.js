include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "casslaw.mm"
include "wbr.mm"
include "cmgm2.mm"
include "csgrp2.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breq12d.mm"
include "df-sgrp2.mm"
include "elrab2.mm"

theorem issgrpALT
  let cB: class B
  let cM: class M
  let c.op: class .o.
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x
  assume ismgmALT.b: |- B = ( Base ` M )
  assume ismgmALT.o: |- .o. = ( +g ` M )


  assert |- ( M e. SGrpALT <-> ( M e. MgmALT /\ .o. assLaw B ) )

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
    casslaw
    wbr
    c.op
    cB
    casslaw
    wbr
    vm
    cM
    cmgm2
    csgrp2
    @0
    cM
    wceq
    #
    @1
    c.op
    @2
    cB
    casslaw
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
    df-sgrp2
    elrab2
end
