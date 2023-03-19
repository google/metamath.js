include "clmod.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "wral.mm"
include "csca.mm"
include "cbs.mm"
include "cpw.mm"
include "crab.mm"
include "cin.mm"
include "cacs.mm"
include "wss.mm"
include "wi.mm"
include "lssss.mm"
include "a1i.mm"
include "inss2.mm"
include "ssrab2.mm"
include "sstri.mm"
include "sseli.mm"
include "elpwid.mm"
include "wb.mm"
include "wa.mm"
include "eqid.mm"
include "islss4.mm"
include "adantr.mm"
include "selpw.mm"
include "weq.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "ralbidv.mm"
include "elrab3.mm"
include "sylbir.mm"
include "adantl.mm"
include "anbi2d.mm"
include "bitr4d.mm"
include "elin.mm"
include "syl6bbr.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "eqrdv.mm"
include "cmre.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mreacs.mm"
include "mp1i.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "subgacs.mm"
include "syl.mm"
include "lmodvscl.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "acsfn1c.mm"
include "sylancr.mm"
include "mreincl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem lssacs
  let cB: class B
  let cS: class S
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  assume lssacs.b: |- B = ( Base ` W )
  assume lssacs.s: |- S = ( LSubSp ` W )


  assert |- ( W e. LMod -> S e. ( ACS ` B ) )

  proof
    cW
    clmod
    wcel
    #
    cS
    cW
    csubg
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    vb
    cv
    #
    wcel
    #
    vy
    @6
    wral
    #
    vx
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wral
    #
    vb
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
    va
    cS
    @14
    @0
    va
    cv
    #
    cB
    wss
    #
    @16
    cS
    wcel
    #
    @16
    @14
    wcel
    #
    @18
    @17
    wi
    @0
    cS
    @16
    cB
    cW
    lssacs.b
    lssacs.s
    lssss
    a1i
    @19
    @17
    wi
    @0
    @19
    @16
    cB
    @14
    @12
    @16
    @14
    @13
    @12
    @1
    @13
    inss2
    @11
    vb
    @12
    ssrab2
    sstri
    sseli
    elpwid
    a1i
    @0
    @17
    @18
    @19
    wb
    @0
    @17
    wa
    #
    @18
    @16
    @1
    wcel
    #
    @16
    @13
    wcel
    #
    wa
    #
    @19
    @20
    @18
    @21
    @5
    @16
    wcel
    #
    vy
    @16
    wral
    #
    vx
    @10
    wral
    #
    wa
    #
    @23
    @0
    @18
    @27
    wb
    @17
    @10
    cS
    @4
    @16
    @9
    cB
    cW
    vx
    vy
    @9
    eqid
    #
    @10
    eqid
    #
    lssacs.b
    @4
    eqid
    #
    lssacs.s
    islss4
    adantr
    @20
    @22
    @26
    @21
    @17
    @22
    @26
    wb
    #
    @0
    @17
    @16
    @12
    wcel
    @31
    va
    cB
    selpw
    @11
    @26
    vb
    @16
    @12
    vb
    va
    weq
    @8
    @25
    vx
    @10
    @7
    @24
    vy
    @6
    @16
    @6
    @16
    @5
    eleq2
    raleqbi1dv
    ralbidv
    elrab3
    sylbir
    adantl
    anbi2d
    bitr4d
    @16
    @1
    @13
    elin
    syl6bbr
    ex
    pm5.21ndd
    eqrdv
    @0
    @15
    @12
    cmre
    cfv
    wcel
    #
    @1
    @15
    wcel
    #
    @13
    @15
    wcel
    #
    @14
    @15
    wcel
    cB
    cvv
    wcel
    #
    @32
    @0
    cB
    cW
    cbs
    cfv
    cvv
    lssacs.b
    cW
    cbs
    fvex
    eqeltri
    #
    cvv
    cB
    mreacs
    mp1i
    @0
    cW
    cgrp
    wcel
    @33
    cW
    lmodgrp
    cB
    cW
    lssacs.b
    subgacs
    syl
    @0
    @35
    @5
    cB
    wcel
    #
    vy
    cB
    wral
    vx
    @10
    wral
    @34
    @36
    @0
    @37
    vx
    vy
    @10
    cB
    @0
    @2
    @10
    wcel
    @3
    cB
    wcel
    @37
    @2
    @4
    @9
    @10
    cB
    cW
    @3
    lssacs.b
    @28
    @30
    @29
    lmodvscl
    3expb
    ralrimivva
    @5
    @10
    cvv
    cB
    vb
    vx
    vy
    acsfn1c
    sylancr
    @1
    @13
    @15
    @12
    mreincl
    syl3anc
    eqeltrd
end
