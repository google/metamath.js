include "cv.mm"
include "chod.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "chos.mm"
include "wcel.mm"
include "cmv.mm"
include "cva.mm"
include "wb.mm"
include "ffvelrni.mm"
include "hvsubadd.mm"
include "syl3anc.mm"
include "wf.mm"
include "hodval.mm"
include "mp3an12.mm"
include "eqeq1d.mm"
include "hosval.mm"
include "3bitr4d.mm"
include "ralbiia.mm"
include "hosubcli.mm"
include "hoeqi.mm"
include "hoaddcli.mm"
include "3bitr3i.mm"

theorem hodsi
  let cR: class R
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hods.1: |- R : ~H --> ~H
  assume hods.2: |- S : ~H --> ~H
  assume hods.3: |- T : ~H --> ~H


  assert |- ( ( R -op S ) = T <-> ( S +op T ) = R )

  proof
    vx
    cv
    #
    cR
    cS
    chod
    co
    #
    cfv
    #
    @0
    cT
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @0
    cS
    cT
    chos
    co
    #
    cfv
    #
    @0
    cR
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @1
    cT
    wceq
    @5
    cR
    wceq
    @4
    @8
    vx
    chil
    @0
    chil
    wcel
    #
    @7
    @0
    cS
    cfv
    #
    cmv
    co
    #
    @3
    wceq
    #
    @10
    @3
    cva
    co
    #
    @7
    wceq
    #
    @4
    @8
    @9
    @7
    chil
    wcel
    @10
    chil
    wcel
    @3
    chil
    wcel
    @12
    @14
    wb
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
    @7
    @10
    @3
    hvsubadd
    syl3anc
    @9
    @2
    @11
    @3
    chil
    chil
    cR
    wf
    chil
    chil
    cS
    wf
    #
    @9
    @2
    @11
    wceq
    hods.1
    hods.2
    @0
    cR
    cS
    hodval
    mp3an12
    eqeq1d
    @9
    @6
    @13
    @7
    @15
    chil
    chil
    cT
    wf
    @9
    @6
    @13
    wceq
    hods.2
    hods.3
    @0
    cS
    cT
    hosval
    mp3an12
    eqeq1d
    3bitr4d
    ralbiia
    vx
    @1
    cT
    cR
    cS
    hods.1
    hods.2
    hosubcli
    hods.3
    hoeqi
    vx
    @5
    cR
    cS
    cT
    hods.2
    hods.3
    hoaddcli
    hods.1
    hoeqi
    3bitr3i
end
