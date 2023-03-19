include "wcel.mm"
include "ccntz.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "ccntr.mm"
include "eqid.mm"
include "cntrval.mm"
include "eqtr4i.mm"
include "eleq2i.mm"
include "cntzi.mm"
include "sylanb.mm"

theorem cntri
  let cB: class B
  let c.pl: class .+
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume cntri.b: |- B = ( Base ` M )
  assume cntri.p: |- .+ = ( +g ` M )
  assume cntri.z: |- Z = ( Cntr ` M )


  assert |- ( ( X e. Z /\ Y e. B ) -> ( X .+ Y ) = ( Y .+ X ) )

  proof
    cX
    cZ
    wcel
    cX
    cB
    cM
    ccntz
    cfv
    #
    cfv
    #
    wcel
    cY
    cB
    wcel
    cX
    cY
    c.pl
    co
    cY
    cX
    c.pl
    co
    wceq
    cZ
    @1
    cX
    cZ
    cM
    ccntr
    cfv
    @1
    cntri.z
    cB
    cM
    @0
    cntri.b
    @0
    eqid
    #
    cntrval
    eqtr4i
    eleq2i
    c.pl
    cB
    cM
    cX
    cY
    @0
    cntri.p
    @2
    cntzi
    sylanb
end
