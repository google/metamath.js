include "cgrp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "csubmnd.mm"
include "cv.mm"
include "cminusg.mm"
include "wral.mm"
include "cpw.mm"
include "crab.mm"
include "cin.mm"
include "cacs.mm"
include "wa.mm"
include "eqid.mm"
include "issubg3.mm"
include "wb.mm"
include "wss.mm"
include "submss.mm"
include "adantl.mm"
include "selpw.mm"
include "sylibr.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "elrab3.mm"
include "syl.mm"
include "pm5.32da.mm"
include "bitr4d.mm"
include "elin.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "cmre.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mreacs.mm"
include "mp1i.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "submacs.mm"
include "grpinvcl.mm"
include "ralrimiva.mm"
include "acsfn1.mm"
include "sylancr.mm"
include "mreincl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem subgacs
  let cB: class B
  let cG: class G
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume subgacs.b: |- B = ( Base ` G )


  assert |- ( G e. Grp -> ( SubGrp ` G ) e. ( ACS ` B ) )

  proof
    cG
    cgrp
    wcel
    #
    cG
    csubg
    cfv
    #
    cG
    csubmnd
    cfv
    #
    vx
    cv
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    vy
    cv
    #
    wcel
    #
    vx
    @6
    wral
    #
    vy
    cB
    cpw
    #
    crab
    #
    cin
    #
    cB
    cacs
    cfv
    #
    @0
    vs
    @1
    @11
    @0
    vs
    cv
    #
    @1
    wcel
    #
    @13
    @2
    wcel
    #
    @13
    @10
    wcel
    #
    wa
    #
    @13
    @11
    wcel
    @0
    @14
    @15
    @5
    @13
    wcel
    #
    vx
    @13
    wral
    #
    wa
    @17
    vx
    @13
    cG
    @4
    @4
    eqid
    #
    issubg3
    @0
    @15
    @16
    @19
    @0
    @15
    wa
    #
    @13
    @9
    wcel
    #
    @16
    @19
    wb
    @21
    @13
    cB
    wss
    #
    @22
    @15
    @23
    @0
    cB
    @13
    cG
    subgacs.b
    submss
    adantl
    vs
    cB
    selpw
    sylibr
    @8
    @19
    vy
    @13
    @9
    @7
    @18
    vx
    @6
    @13
    @6
    @13
    @5
    eleq2
    raleqbi1dv
    elrab3
    syl
    pm5.32da
    bitr4d
    @13
    @2
    @10
    elin
    syl6bbr
    eqrdv
    @0
    @12
    @9
    cmre
    cfv
    wcel
    #
    @2
    @12
    wcel
    #
    @10
    @12
    wcel
    #
    @11
    @12
    wcel
    cB
    cvv
    wcel
    #
    @24
    @0
    cB
    cG
    cbs
    cfv
    cvv
    subgacs.b
    cG
    cbs
    fvex
    eqeltri
    #
    cvv
    cB
    mreacs
    mp1i
    @0
    cG
    cmnd
    wcel
    @25
    cG
    grpmnd
    cB
    cG
    subgacs.b
    submacs
    syl
    @0
    @27
    @5
    cB
    wcel
    #
    vx
    cB
    wral
    @26
    @28
    @0
    @29
    vx
    cB
    cB
    cG
    @4
    @3
    subgacs.b
    @20
    grpinvcl
    ralrimiva
    @5
    cvv
    cB
    vy
    vx
    acsfn1
    sylancr
    @2
    @10
    @12
    @9
    mreincl
    syl3anc
    eqeltrd
end
