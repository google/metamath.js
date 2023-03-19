include "cmgm.mm"
include "wcel.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "eqid.mm"
include "mgmcl.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "plusffval.mm"
include "fmpt2.mm"
include "sylib.mm"

theorem mgmplusf
  let cB: class B
  let c.pd: class .+^
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  assume mgmplusf.1: |- B = ( Base ` M )
  assume mgmplusf.2: |- .+^ = ( +f ` M )


  assert |- ( M e. Mgm -> .+^ : ( B X. B ) --> B )

  proof
    cM
    cmgm
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    cB
    wcel
    #
    vy
    cB
    wral
    vx
    cB
    wral
    cB
    cB
    cxp
    cB
    c.pd
    wf
    @0
    @5
    vx
    vy
    cB
    cB
    @0
    @1
    cB
    wcel
    @2
    cB
    wcel
    @5
    cB
    cM
    @1
    @2
    @3
    mgmplusf.1
    @3
    eqid
    #
    mgmcl
    3expb
    ralrimivva
    vx
    vy
    cB
    cB
    @4
    cB
    c.pd
    vx
    vy
    cB
    @3
    c.pd
    cM
    mgmplusf.1
    @6
    mgmplusf.2
    plusffval
    fmpt2
    sylib
end
