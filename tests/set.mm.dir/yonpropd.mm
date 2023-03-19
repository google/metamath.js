include "coppc.mm"
include "cfv.mm"
include "cop.mm"
include "chof.mm"
include "ccurf.mm"
include "co.mm"
include "cyon.mm"
include "chomf.mm"
include "crn.mm"
include "csetc.mm"
include "oppchomfpropd.mm"
include "oppccomfpropd.mm"
include "ccat.mm"
include "wcel.mm"
include "eqid.mm"
include "oppccat.mm"
include "syl.mm"
include "cvv.mm"
include "fvex.mm"
include "rnex.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "oppchofcl.mm"
include "curfpropd.mm"
include "hofpropd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "yonval.mm"
include "3eqtr4d.mm"

theorem yonpropd
  let wph: wff ph
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  assume hofpropd.1: |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )
  assume hofpropd.2: |- ( ph -> ( comf ` C ) = ( comf ` D ) )
  assume hofpropd.c: |- ( ph -> C e. Cat )
  assume hofpropd.d: |- ( ph -> D e. Cat )


  assert |- ( ph -> ( Yon ` C ) = ( Yon ` D ) )

  proof
    wph
    cC
    cC
    coppc
    cfv
    #
    cop
    @0
    chof
    cfv
    #
    ccurf
    co
    #
    cD
    cD
    coppc
    cfv
    #
    cop
    #
    @3
    chof
    cfv
    #
    ccurf
    co
    #
    cC
    cyon
    cfv
    #
    cD
    cyon
    cfv
    #
    wph
    @2
    @4
    @1
    ccurf
    co
    @6
    wph
    cC
    cD
    @0
    @3
    cC
    chomf
    cfv
    #
    crn
    #
    csetc
    cfv
    #
    @1
    hofpropd.1
    hofpropd.2
    wph
    cC
    cD
    hofpropd.1
    oppchomfpropd
    #
    wph
    cC
    cD
    hofpropd.1
    hofpropd.2
    oppccomfpropd
    #
    hofpropd.c
    hofpropd.d
    wph
    cC
    ccat
    wcel
    @0
    ccat
    wcel
    hofpropd.c
    cC
    @0
    @0
    eqid
    #
    oppccat
    syl
    #
    wph
    cD
    ccat
    wcel
    @3
    ccat
    wcel
    hofpropd.d
    cD
    @3
    @3
    eqid
    #
    oppccat
    syl
    #
    wph
    cC
    @11
    @10
    @1
    @0
    cvv
    @14
    @1
    eqid
    #
    @11
    eqid
    hofpropd.c
    @10
    cvv
    wcel
    wph
    @9
    cC
    chomf
    fvex
    rnex
    a1i
    @10
    @10
    wss
    wph
    @10
    ssid
    a1i
    oppchofcl
    curfpropd
    wph
    @1
    @5
    @4
    ccurf
    wph
    @0
    @3
    @12
    @13
    @15
    @17
    hofpropd
    oveq2d
    eqtrd
    wph
    cC
    @1
    @0
    @7
    @7
    eqid
    hofpropd.c
    @14
    @18
    yonval
    wph
    cD
    @5
    @3
    @8
    @8
    eqid
    hofpropd.d
    @16
    @5
    eqid
    yonval
    3eqtr4d
end
