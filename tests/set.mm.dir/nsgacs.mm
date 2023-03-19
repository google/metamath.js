include "cgrp.mm"
include "wcel.mm"
include "cnsg.mm"
include "cfv.mm"
include "csubg.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "csg.mm"
include "wral.mm"
include "cpw.mm"
include "crab.mm"
include "cin.mm"
include "cacs.mm"
include "wa.mm"
include "wb.mm"
include "wss.mm"
include "subgss.mm"
include "selpw.mm"
include "sylibr.mm"
include "weq.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "ralbidv.mm"
include "elrab3.mm"
include "syl.mm"
include "bicomd.mm"
include "pm5.32i.mm"
include "eqid.mm"
include "isnsg3.mm"
include "elin.mm"
include "3bitr4i.mm"
include "eqriv.mm"
include "cmre.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mreacs.mm"
include "mp1i.mm"
include "subgacs.mm"
include "simpl.mm"
include "grpcl.mm"
include "3expb.mm"
include "simprl.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "ralrimivva.mm"
include "acsfn1c.mm"
include "sylancr.mm"
include "mreincl.mm"
include "syl5eqel.mm"

theorem nsgacs
  let cB: class B
  let cG: class G
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume subgacs.b: |- B = ( Base ` G )


  assert |- ( G e. Grp -> ( NrmSGrp ` G ) e. ( ACS ` B ) )

  proof
    cG
    cgrp
    wcel
    #
    cG
    cnsg
    cfv
    #
    cG
    csubg
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @3
    cG
    csg
    cfv
    #
    co
    #
    vz
    cv
    #
    wcel
    #
    vy
    @9
    wral
    #
    vx
    cB
    wral
    #
    vz
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
    vs
    @1
    @15
    vs
    cv
    #
    @2
    wcel
    #
    @8
    @17
    wcel
    #
    vy
    @17
    wral
    #
    vx
    cB
    wral
    #
    wa
    @18
    @17
    @14
    wcel
    #
    wa
    @17
    @1
    wcel
    @17
    @15
    wcel
    @18
    @21
    @22
    @18
    @22
    @21
    @18
    @17
    @13
    wcel
    #
    @22
    @21
    wb
    @18
    @17
    cB
    wss
    @23
    cB
    @17
    cG
    subgacs.b
    subgss
    vs
    cB
    selpw
    sylibr
    @12
    @21
    vz
    @17
    @13
    vz
    vs
    weq
    @11
    @20
    vx
    cB
    @10
    @19
    vy
    @9
    @17
    @9
    @17
    @8
    eleq2
    raleqbi1dv
    ralbidv
    elrab3
    syl
    bicomd
    pm5.32i
    vx
    vy
    @5
    @17
    cG
    @7
    cB
    subgacs.b
    @5
    eqid
    #
    @7
    eqid
    #
    isnsg3
    @17
    @2
    @14
    elin
    3bitr4i
    eqriv
    @0
    @16
    @13
    cmre
    cfv
    wcel
    #
    @2
    @16
    wcel
    @14
    @16
    wcel
    #
    @15
    @16
    wcel
    cB
    cvv
    wcel
    #
    @26
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
    cB
    cG
    subgacs.b
    subgacs
    @0
    @28
    @8
    cB
    wcel
    #
    vy
    cB
    wral
    vx
    cB
    wral
    @27
    @29
    @0
    @30
    vx
    vy
    cB
    cB
    @0
    @3
    cB
    wcel
    #
    @4
    cB
    wcel
    #
    wa
    #
    wa
    @0
    @6
    cB
    wcel
    #
    @31
    @30
    @0
    @33
    simpl
    @0
    @31
    @32
    @34
    cB
    @5
    cG
    @3
    @4
    subgacs.b
    @24
    grpcl
    3expb
    @0
    @31
    @32
    simprl
    cB
    cG
    @7
    @6
    @3
    subgacs.b
    @25
    grpsubcl
    syl3anc
    ralrimivva
    @8
    cB
    cvv
    cB
    vz
    vx
    vy
    acsfn1c
    sylancr
    @2
    @14
    @16
    @13
    mreincl
    syl3anc
    syl5eqel
end
