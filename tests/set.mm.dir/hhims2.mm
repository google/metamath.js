include "cims.mm"
include "cfv.mm"
include "cno.mm"
include "cmv.mm"
include "ccom.mm"
include "eqid.mm"
include "hhims.mm"
include "eqtr4i.mm"

theorem hhims2
  let cD: class D
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume hhnv.1: |- U = <. <. +h , .h >. , normh >.
  assume hhims2.2: |- D = ( IndMet ` U )


  assert |- D = ( normh o. -h )

  proof
    cD
    cU
    cims
    cfv
    cno
    cmv
    ccom
    #
    hhims2.2
    @0
    cU
    hhnv.1
    @0
    eqid
    hhims
    eqtr4i
end
