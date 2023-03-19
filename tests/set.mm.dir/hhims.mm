include "cno.mm"
include "cmv.mm"
include "ccom.mm"
include "cims.mm"
include "cfv.mm"
include "cnv.mm"
include "wcel.mm"
include "wceq.mm"
include "hhnv.mm"
include "hhvs.mm"
include "hhnm.mm"
include "eqid.mm"
include "imsval.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem hhims
  let cD: class D
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume hhnv.1: |- U = <. <. +h , .h >. , normh >.
  assume hhims.2: |- D = ( normh o. -h )


  assert |- D = ( IndMet ` U )

  proof
    cD
    cno
    cmv
    ccom
    #
    cU
    cims
    cfv
    #
    hhims.2
    cU
    cnv
    wcel
    @1
    @0
    wceq
    cU
    hhnv.1
    hhnv
    @1
    cU
    cmv
    cno
    cU
    hhnv.1
    hhvs
    cU
    hhnv.1
    hhnm
    @1
    eqid
    imsval
    ax-mp
    eqtr4i
end
