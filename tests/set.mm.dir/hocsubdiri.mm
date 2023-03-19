include "cv.mm"
include "chod.mm"
include "co.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "hosubcli.mm"
include "hocoi.mm"
include "cmv.mm"
include "wf.mm"
include "hocofi.mm"
include "hodval.mm"
include "mp3an12.mm"
include "ffvelrni.mm"
include "syl.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "rgen.mm"
include "hoeqi.mm"
include "mpbi.mm"

theorem hocsubdiri
  let cR: class R
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hods.1: |- R : ~H --> ~H
  assume hods.2: |- S : ~H --> ~H
  assume hods.3: |- T : ~H --> ~H


  assert |- ( ( R -op S ) o. T ) = ( ( R o. T ) -op ( S o. T ) )

  proof
    vx
    cv
    #
    cR
    cS
    chod
    co
    #
    cT
    ccom
    #
    cfv
    #
    @0
    cR
    cT
    ccom
    #
    cS
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
    @2
    @6
    wceq
    @8
    vx
    chil
    @0
    chil
    wcel
    #
    @3
    @0
    cT
    cfv
    #
    @1
    cfv
    #
    @7
    @0
    @1
    cT
    cR
    cS
    hods.1
    hods.2
    hosubcli
    #
    hods.3
    hocoi
    @9
    @7
    @0
    @4
    cfv
    #
    @0
    @5
    cfv
    #
    cmv
    co
    #
    @11
    chil
    chil
    @4
    wf
    chil
    chil
    @5
    wf
    @9
    @7
    @15
    wceq
    cR
    cT
    hods.1
    hods.3
    hocofi
    #
    cS
    cT
    hods.2
    hods.3
    hocofi
    #
    @0
    @4
    @5
    hodval
    mp3an12
    @9
    @11
    @10
    cR
    cfv
    #
    @10
    cS
    cfv
    #
    cmv
    co
    #
    @15
    @9
    @10
    chil
    wcel
    #
    @11
    @20
    wceq
    #
    chil
    chil
    @0
    cT
    hods.3
    ffvelrni
    chil
    chil
    cR
    wf
    chil
    chil
    cS
    wf
    @21
    @22
    hods.1
    hods.2
    @10
    cR
    cS
    hodval
    mp3an12
    syl
    @9
    @13
    @18
    @14
    @19
    cmv
    @0
    cR
    cT
    hods.1
    hods.3
    hocoi
    @0
    cS
    cT
    hods.2
    hods.3
    hocoi
    oveq12d
    eqtr4d
    eqtr4d
    eqtr4d
    rgen
    vx
    @2
    @6
    @1
    cT
    @12
    hods.3
    hocofi
    @4
    @5
    @16
    @17
    hosubcli
    hoeqi
    mpbi
end
