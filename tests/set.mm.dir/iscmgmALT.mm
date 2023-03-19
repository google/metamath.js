include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "ccomlaw.mm"
include "wbr.mm"
include "cmgm2.mm"
include "ccmgm2.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq12d.mm"
include "breq12i.mm"
include "syl6bbr.mm"
include "df-cmgm2.mm"
include "elrab2.mm"

theorem iscmgmALT
  let cB: class B
  let cM: class M
  let c.op: class .o.
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x
  assume ismgmALT.b: |- B = ( Base ` M )
  assume ismgmALT.o: |- .o. = ( +g ` M )


  assert |- ( M e. CMgmALT <-> ( M e. MgmALT /\ .o. comLaw B ) )

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
    ccomlaw
    wbr
    #
    c.op
    cB
    ccomlaw
    wbr
    #
    vm
    cM
    cmgm2
    ccmgm2
    @0
    cM
    wceq
    #
    @3
    cM
    cplusg
    cfv
    #
    cM
    cbs
    cfv
    #
    ccomlaw
    wbr
    @4
    @5
    @1
    @6
    @2
    @7
    ccomlaw
    @0
    cM
    cplusg
    fveq2
    @0
    cM
    cbs
    fveq2
    breq12d
    c.op
    @6
    cB
    @7
    ccomlaw
    ismgmALT.o
    ismgmALT.b
    breq12i
    syl6bbr
    vm
    df-cmgm2
    elrab2
end
