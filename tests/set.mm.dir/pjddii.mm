include "cv.mm"
include "cpjh.mm"
include "cfv.mm"
include "chod.mm"
include "co.mm"
include "ccom.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "cmv.mm"
include "ffvelrni.mm"
include "pjsubi.mm"
include "syl2anc.mm"
include "wf.mm"
include "hodval.mm"
include "mp3an12.mm"
include "fveq2d.mm"
include "pjfi.mm"
include "hocoi.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "hosubcli.mm"
include "hocofi.mm"
include "rgen.mm"
include "hoeqi.mm"
include "mpbi.mm"

theorem pjddii
  let cS: class S
  let cT: class T
  let cH: class H
  let vx: setvar x
  assume pjsdi.1: |- H e. CH
  assume pjsdi.2: |- S : ~H --> ~H
  assume pjsdi.3: |- T : ~H --> ~H


  assert |- ( ( projh ` H ) o. ( S -op T ) ) = ( ( ( projh ` H ) o. S ) -op ( ( projh ` H ) o. T ) )

  proof
    vx
    cv
    #
    cH
    cpjh
    cfv
    #
    cS
    cT
    chod
    co
    #
    ccom
    #
    cfv
    #
    @0
    @1
    cS
    ccom
    #
    @1
    cT
    ccom
    #
    chod
    co
    #
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @3
    @7
    wceq
    @9
    vx
    chil
    @0
    chil
    wcel
    #
    @0
    @2
    cfv
    #
    @1
    cfv
    #
    @0
    @5
    cfv
    #
    @0
    @6
    cfv
    #
    cmv
    co
    #
    @4
    @8
    @10
    @0
    cS
    cfv
    #
    @0
    cT
    cfv
    #
    cmv
    co
    #
    @1
    cfv
    #
    @16
    @1
    cfv
    #
    @17
    @1
    cfv
    #
    cmv
    co
    #
    @12
    @15
    @10
    @16
    chil
    wcel
    @17
    chil
    wcel
    @19
    @22
    wceq
    chil
    chil
    @0
    cS
    pjsdi.2
    ffvelrni
    chil
    chil
    @0
    cT
    pjsdi.3
    ffvelrni
    @16
    @17
    cH
    pjsdi.1
    pjsubi
    syl2anc
    @10
    @11
    @18
    @1
    chil
    chil
    cS
    wf
    chil
    chil
    cT
    wf
    @10
    @11
    @18
    wceq
    pjsdi.2
    pjsdi.3
    @0
    cS
    cT
    hodval
    mp3an12
    fveq2d
    @10
    @13
    @20
    @14
    @21
    cmv
    @0
    @1
    cS
    cH
    pjsdi.1
    pjfi
    #
    pjsdi.2
    hocoi
    @0
    @1
    cT
    @23
    pjsdi.3
    hocoi
    oveq12d
    3eqtr4d
    @0
    @1
    @2
    @23
    cS
    cT
    pjsdi.2
    pjsdi.3
    hosubcli
    #
    hocoi
    chil
    chil
    @5
    wf
    chil
    chil
    @6
    wf
    @10
    @8
    @15
    wceq
    @1
    cS
    @23
    pjsdi.2
    hocofi
    #
    @1
    cT
    @23
    pjsdi.3
    hocofi
    #
    @0
    @5
    @6
    hodval
    mp3an12
    3eqtr4d
    rgen
    vx
    @3
    @7
    @1
    @2
    @23
    @24
    hocofi
    @5
    @6
    @25
    @26
    hosubcli
    hoeqi
    mpbi
end
