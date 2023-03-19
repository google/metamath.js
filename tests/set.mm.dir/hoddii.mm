include "cv.mm"
include "chod.mm"
include "co.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "cmv.mm"
include "ffvelrni.mm"
include "lnopsubi.mm"
include "syl2anc.mm"
include "wf.mm"
include "hodval.mm"
include "mp3an12.mm"
include "fveq2d.mm"
include "lnopfi.mm"
include "hocoi.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "hosubcli.mm"
include "hocofi.mm"
include "rgen.mm"
include "hoeqi.mm"
include "mpbi.mm"

theorem hoddii
  let cR: class R
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hoddi.1: |- R e. LinOp
  assume hoddi.2: |- S : ~H --> ~H
  assume hoddi.3: |- T : ~H --> ~H


  assert |- ( R o. ( S -op T ) ) = ( ( R o. S ) -op ( R o. T ) )

  proof
    vx
    cv
    #
    cR
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
    cR
    cS
    ccom
    #
    cR
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
    @0
    @1
    cfv
    #
    cR
    cfv
    #
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
    @3
    @7
    @9
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
    cR
    cfv
    #
    @15
    cR
    cfv
    #
    @16
    cR
    cfv
    #
    cmv
    co
    #
    @11
    @14
    @9
    @15
    chil
    wcel
    @16
    chil
    wcel
    @18
    @21
    wceq
    chil
    chil
    @0
    cS
    hoddi.2
    ffvelrni
    chil
    chil
    @0
    cT
    hoddi.3
    ffvelrni
    @15
    @16
    cR
    hoddi.1
    lnopsubi
    syl2anc
    @9
    @10
    @17
    cR
    chil
    chil
    cS
    wf
    chil
    chil
    cT
    wf
    @9
    @10
    @17
    wceq
    hoddi.2
    hoddi.3
    @0
    cS
    cT
    hodval
    mp3an12
    fveq2d
    @9
    @12
    @19
    @13
    @20
    cmv
    @0
    cR
    cS
    cR
    hoddi.1
    lnopfi
    #
    hoddi.2
    hocoi
    @0
    cR
    cT
    @22
    hoddi.3
    hocoi
    oveq12d
    3eqtr4d
    @0
    cR
    @1
    @22
    cS
    cT
    hoddi.2
    hoddi.3
    hosubcli
    #
    hocoi
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
    @14
    wceq
    cR
    cS
    @22
    hoddi.2
    hocofi
    #
    cR
    cT
    @22
    hoddi.3
    hocofi
    #
    @0
    @4
    @5
    hodval
    mp3an12
    3eqtr4d
    rgen
    vx
    @2
    @6
    cR
    @1
    @22
    @23
    hocofi
    @4
    @5
    @24
    @25
    hosubcli
    hoeqi
    mpbi
end
