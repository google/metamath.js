include "cdr.mm"
include "wcel.mm"
include "csdrg.mm"
include "cfv.mm"
include "csubrg.mm"
include "cv.mm"
include "c0g.mm"
include "wceq.mm"
include "cinvr.mm"
include "cif.mm"
include "wral.mm"
include "cpw.mm"
include "crab.mm"
include "cin.mm"
include "cacs.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "w3a.mm"
include "eqid.mm"
include "issdrg2.mm"
include "3anass.mm"
include "bitri.mm"
include "baib.mm"
include "wb.mm"
include "wss.mm"
include "subrgss.mm"
include "selpw.mm"
include "sylibr.mm"
include "adantl.mm"
include "wi.mm"
include "iftrue.mm"
include "eleq1d.mm"
include "biimprd.mm"
include "eldifsni.mm"
include "necon2bi.mm"
include "pm2.21d.mm"
include "2thd.mm"
include "wne.mm"
include "eldifsn.mm"
include "rbaibr.mm"
include "ifnefalse.mm"
include "imbi12d.mm"
include "pm2.61ine.mm"
include "ralbii2.mm"
include "difeq1.mm"
include "eleq2.mm"
include "raleqbidv.mm"
include "syl5bb.mm"
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
include "crg.mm"
include "drngring.mm"
include "subrgacs.mm"
include "simplr.mm"
include "wn.mm"
include "df-ne.mm"
include "drnginvrcl.mm"
include "3expa.mm"
include "sylan2br.mm"
include "ifclda.mm"
include "ralrimiva.mm"
include "acsfn1.mm"
include "sylancr.mm"
include "mreincl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem sdrgacs
  let cB: class B
  let cR: class R
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume subrgacs.b: |- B = ( Base ` R )


  assert |- ( R e. DivRing -> ( SubDRing ` R ) e. ( ACS ` B ) )

  proof
    cR
    cdr
    wcel
    #
    cR
    csdrg
    cfv
    #
    cR
    csubrg
    cfv
    #
    vx
    cv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    @3
    @3
    cR
    cinvr
    cfv
    #
    cfv
    #
    cif
    #
    vy
    cv
    #
    wcel
    #
    vx
    @9
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
    @14
    @0
    vs
    cv
    #
    @1
    wcel
    #
    @16
    @2
    wcel
    #
    @16
    @13
    wcel
    #
    wa
    #
    @16
    @14
    wcel
    @0
    @17
    @18
    @7
    @16
    wcel
    #
    vx
    @16
    @4
    csn
    #
    cdif
    #
    wral
    #
    wa
    #
    @20
    @17
    @0
    @25
    @17
    @0
    @18
    @24
    w3a
    @0
    @25
    wa
    vx
    cR
    @16
    @6
    @4
    @6
    eqid
    #
    @4
    eqid
    #
    issdrg2
    @0
    @18
    @24
    3anass
    bitri
    baib
    @0
    @18
    @19
    @24
    @0
    @18
    wa
    @16
    @12
    wcel
    #
    @19
    @24
    wb
    @18
    @28
    @0
    @18
    @16
    cB
    wss
    @28
    @16
    cB
    cR
    subrgacs.b
    subrgss
    vs
    cB
    selpw
    sylibr
    adantl
    @11
    @24
    vy
    @16
    @12
    @11
    @7
    @9
    wcel
    #
    vx
    @9
    @22
    cdif
    #
    wral
    @9
    @16
    wceq
    #
    @24
    @10
    @29
    vx
    @9
    @30
    @3
    @9
    wcel
    #
    @10
    wi
    #
    @3
    @30
    wcel
    #
    @29
    wi
    #
    wb
    @3
    @4
    @5
    @33
    @35
    @5
    @10
    @32
    @5
    @8
    @3
    @9
    @5
    @3
    @7
    iftrue
    eleq1d
    biimprd
    @5
    @34
    @29
    @34
    @3
    @4
    @3
    @9
    @4
    eldifsni
    necon2bi
    pm2.21d
    2thd
    @3
    @4
    wne
    #
    @32
    @34
    @10
    @29
    @34
    @32
    @36
    @3
    @9
    @4
    eldifsn
    rbaibr
    @36
    @8
    @7
    @9
    @3
    @4
    @3
    @7
    ifnefalse
    eleq1d
    imbi12d
    pm2.61ine
    ralbii2
    @31
    @29
    @21
    vx
    @30
    @23
    @9
    @16
    @22
    difeq1
    @9
    @16
    @7
    eleq2
    raleqbidv
    syl5bb
    elrab3
    syl
    pm5.32da
    bitr4d
    @16
    @2
    @13
    elin
    syl6bbr
    eqrdv
    @0
    @15
    @12
    cmre
    cfv
    wcel
    #
    @2
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
    @37
    @0
    cB
    cR
    cbs
    cfv
    cvv
    subrgacs.b
    cR
    cbs
    fvex
    eqeltri
    #
    cvv
    cB
    mreacs
    mp1i
    @0
    cR
    crg
    wcel
    @38
    cR
    drngring
    cB
    cR
    subrgacs.b
    subrgacs
    syl
    @0
    @40
    @8
    cB
    wcel
    #
    vx
    cB
    wral
    @39
    @41
    @0
    @42
    vx
    cB
    @0
    @3
    cB
    wcel
    #
    wa
    #
    @5
    @3
    @7
    cB
    @0
    @43
    @5
    simplr
    @5
    wn
    @44
    @36
    @7
    cB
    wcel
    #
    @3
    @4
    df-ne
    @0
    @43
    @36
    @45
    cB
    cR
    @6
    @3
    @4
    subrgacs.b
    @27
    @26
    drnginvrcl
    3expa
    sylan2br
    ifclda
    ralrimiva
    @8
    cvv
    cB
    vy
    vx
    acsfn1
    sylancr
    @2
    @13
    @15
    @12
    mreincl
    syl3anc
    eqeltrd
end
