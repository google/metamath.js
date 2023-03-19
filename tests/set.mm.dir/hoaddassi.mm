include "cv.mm"
include "chos.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "cva.mm"
include "wf.mm"
include "hosval.mm"
include "mp3an12.mm"
include "oveq1d.mm"
include "hoaddcli.mm"
include "oveq2d.mm"
include "ffvelrni.mm"
include "ax-hvass.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"
include "rgen.mm"
include "hoeqi.mm"
include "mpbi.mm"

theorem hoaddassi
  let cR: class R
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hods.1: |- R : ~H --> ~H
  assume hods.2: |- S : ~H --> ~H
  assume hods.3: |- T : ~H --> ~H


  assert |- ( ( R +op S ) +op T ) = ( R +op ( S +op T ) )

  proof
    vx
    cv
    #
    cR
    cS
    chos
    co
    #
    cT
    chos
    co
    #
    cfv
    #
    @0
    cR
    cS
    cT
    chos
    co
    #
    chos
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
    @5
    wceq
    @7
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
    @0
    cT
    cfv
    #
    cva
    co
    #
    @0
    cR
    cfv
    #
    @0
    cS
    cfv
    #
    cva
    co
    #
    @10
    cva
    co
    #
    @3
    @6
    @8
    @9
    @14
    @10
    cva
    chil
    chil
    cR
    wf
    #
    chil
    chil
    cS
    wf
    #
    @8
    @9
    @14
    wceq
    hods.1
    hods.2
    @0
    cR
    cS
    hosval
    mp3an12
    oveq1d
    chil
    chil
    @1
    wf
    chil
    chil
    cT
    wf
    #
    @8
    @3
    @11
    wceq
    cR
    cS
    hods.1
    hods.2
    hoaddcli
    #
    hods.3
    @0
    @1
    cT
    hosval
    mp3an12
    @8
    @12
    @0
    @4
    cfv
    #
    cva
    co
    #
    @12
    @13
    @10
    cva
    co
    #
    cva
    co
    #
    @6
    @15
    @8
    @20
    @22
    @12
    cva
    @17
    @18
    @8
    @20
    @22
    wceq
    hods.2
    hods.3
    @0
    cS
    cT
    hosval
    mp3an12
    oveq2d
    @16
    chil
    chil
    @4
    wf
    @8
    @6
    @21
    wceq
    hods.1
    cS
    cT
    hods.2
    hods.3
    hoaddcli
    #
    @0
    cR
    @4
    hosval
    mp3an12
    @8
    @12
    chil
    wcel
    @13
    chil
    wcel
    @10
    chil
    wcel
    @15
    @23
    wceq
    chil
    chil
    @0
    cR
    hods.1
    ffvelrni
    chil
    chil
    @0
    cS
    hods.2
    ffvelrni
    chil
    chil
    @0
    cT
    hods.3
    ffvelrni
    @12
    @13
    @10
    ax-hvass
    syl3anc
    3eqtr4d
    3eqtr4d
    rgen
    vx
    @2
    @5
    @1
    cT
    @19
    hods.3
    hoaddcli
    cR
    @4
    hods.1
    @24
    hoaddcli
    hoeqi
    mpbi
end
