include "cgrp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wss.mm"
include "cnsg.mm"
include "cbs.mm"
include "ccntz.mm"
include "ccntr.mm"
include "eqid.mm"
include "cntrval.mm"
include "eqtr4i.mm"
include "ssid.mm"
include "cntzsubg.mm"
include "mpan2.mm"
include "syl5eqel.mm"
include "cntrsubgnsg.mm"
include "sylancl.mm"

theorem cntrnsg
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  assume cntrnsg.z: |- Z = ( Cntr ` M )


  assert |- ( M e. Grp -> Z e. ( NrmSGrp ` M ) )

  proof
    cM
    cgrp
    wcel
    #
    cZ
    cM
    csubg
    cfv
    #
    wcel
    cZ
    cZ
    wss
    cZ
    cM
    cnsg
    cfv
    wcel
    @0
    cZ
    cM
    cbs
    cfv
    #
    cM
    ccntz
    cfv
    #
    cfv
    #
    @1
    cZ
    cM
    ccntr
    cfv
    @4
    cntrnsg.z
    @2
    cM
    @3
    @2
    eqid
    #
    @3
    eqid
    #
    cntrval
    eqtr4i
    @0
    @2
    @2
    wss
    @4
    @1
    wcel
    @2
    ssid
    @2
    @2
    cM
    @3
    @5
    @6
    cntzsubg
    mpan2
    syl5eqel
    cZ
    ssid
    cM
    cZ
    cZ
    cntrnsg.z
    cntrsubgnsg
    sylancl
end
