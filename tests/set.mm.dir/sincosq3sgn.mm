include "cpi.mm"
include "c3.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cioo.mm"
include "wcel.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "ccos.mm"
include "wa.mm"
include "wb.mm"
include "pire.mm"
include "3re.mm"
include "halfpire.mm"
include "remulcli.mm"
include "cxr.mm"
include "rexr.mm"
include "elioo2.mm"
include "syl2an.mm"
include "mp2an.mm"
include "cmin.mm"
include "cneg.mm"
include "caddc.mm"
include "pidiv2halves.mm"
include "breq1i.mm"
include "ltaddsub.mm"
include "mp3an12.mm"
include "syl5bbr.mm"
include "ltsubadd.mm"
include "mp3an23.mm"
include "c1.mm"
include "df-3.mm"
include "oveq1i.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "recni.mm"
include "adddiri.mm"
include "2ne0.mm"
include "divcan2i.mm"
include "mulid2i.mm"
include "oveq12i.mm"
include "3eqtrri.mm"
include "breq2i.mm"
include "syl6rbb.mm"
include "anbi12d.mm"
include "resubcl.mm"
include "mpan2.mm"
include "sincosq2sgn.mm"
include "ancom.mm"
include "3imtr3i.mm"
include "syl3an1.mm"
include "3expib.mm"
include "sylbid.mm"
include "resincld.mm"
include "lt0neg2d.mm"
include "anbi2d.mm"
include "sylibd.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "pncan3.mm"
include "sylancr.mm"
include "fveq2d.mm"
include "recnd.mm"
include "sinhalfpip.mm"
include "syl.mm"
include "eqtr3d.mm"
include "breq1d.mm"
include "coshalfpip.mm"
include "sylibrd.mm"
include "3impib.mm"
include "sylbi.mm"

theorem sincosq3sgn
  let cA: class A


  assert |- ( A e. ( _pi (,) ( 3 x. ( _pi / 2 ) ) ) -> ( ( sin ` A ) < 0 /\ ( cos ` A ) < 0 ) )

  proof
    cA
    cpi
    c3
    cpi
    c2
    cdiv
    co
    #
    cmul
    co
    #
    cioo
    co
    wcel
    #
    cA
    cr
    wcel
    #
    cpi
    cA
    clt
    wbr
    #
    cA
    @1
    clt
    wbr
    #
    w3a
    #
    cA
    csin
    cfv
    #
    cc0
    clt
    wbr
    #
    cA
    ccos
    cfv
    #
    cc0
    clt
    wbr
    #
    wa
    #
    cpi
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @2
    @6
    wb
    #
    pire
    c3
    @0
    3re
    halfpire
    remulcli
    @12
    cpi
    cxr
    wcel
    #
    @1
    cxr
    wcel
    @14
    @13
    cpi
    rexr
    #
    @1
    rexr
    cpi
    @1
    cA
    elioo2
    syl2an
    mp2an
    @3
    @4
    @5
    @11
    @3
    @4
    @5
    wa
    #
    cA
    @0
    cmin
    co
    #
    ccos
    cfv
    #
    cc0
    clt
    wbr
    #
    @18
    csin
    cfv
    #
    cneg
    #
    cc0
    clt
    wbr
    #
    wa
    #
    @11
    @3
    @17
    @20
    cc0
    @21
    clt
    wbr
    #
    wa
    #
    @24
    @3
    @17
    @0
    @18
    clt
    wbr
    #
    @18
    cpi
    clt
    wbr
    #
    wa
    @26
    @3
    @4
    @27
    @5
    @28
    @4
    @0
    @0
    caddc
    co
    #
    cA
    clt
    wbr
    #
    @3
    @27
    @29
    cpi
    cA
    clt
    pidiv2halves
    breq1i
    @0
    cr
    wcel
    #
    @31
    @3
    @30
    @27
    wb
    halfpire
    halfpire
    @0
    @0
    cA
    ltaddsub
    mp3an12
    syl5bbr
    @3
    @28
    cA
    cpi
    @0
    caddc
    co
    #
    clt
    wbr
    #
    @5
    @3
    @31
    @12
    @28
    @33
    wb
    halfpire
    pire
    cA
    @0
    cpi
    ltsubadd
    mp3an23
    @32
    @1
    cA
    clt
    @1
    c2
    c1
    caddc
    co
    #
    @0
    cmul
    co
    c2
    @0
    cmul
    co
    #
    c1
    @0
    cmul
    co
    #
    caddc
    co
    @32
    c3
    @34
    @0
    cmul
    df-3
    oveq1i
    c2
    c1
    @0
    2cn
    ax-1cn
    @0
    halfpire
    recni
    #
    adddiri
    @35
    cpi
    @36
    @0
    caddc
    cpi
    c2
    cpi
    pire
    recni
    2cn
    2ne0
    divcan2i
    @0
    @37
    mulid2i
    oveq12i
    3eqtrri
    breq2i
    syl6rbb
    anbi12d
    @3
    @27
    @28
    @26
    @3
    @18
    cr
    wcel
    #
    @27
    @28
    @26
    @3
    @31
    @38
    halfpire
    cA
    @0
    resubcl
    mpan2
    #
    @18
    @0
    cpi
    cioo
    co
    wcel
    #
    @25
    @20
    wa
    @38
    @27
    @28
    w3a
    #
    @26
    @18
    sincosq2sgn
    @31
    @12
    @40
    @41
    wb
    #
    halfpire
    pire
    @31
    @0
    cxr
    wcel
    @15
    @42
    @12
    @0
    rexr
    @16
    @0
    cpi
    @18
    elioo2
    syl2an
    mp2an
    @25
    @20
    ancom
    3imtr3i
    syl3an1
    3expib
    sylbid
    @3
    @25
    @23
    @20
    @3
    @21
    @3
    @18
    @39
    resincld
    lt0neg2d
    anbi2d
    sylibd
    @3
    @8
    @20
    @10
    @23
    @3
    @7
    @19
    cc0
    clt
    @3
    @0
    @18
    caddc
    co
    #
    csin
    cfv
    #
    @7
    @19
    @3
    @43
    cA
    csin
    @3
    @0
    cc
    wcel
    cA
    cc
    wcel
    @43
    cA
    wceq
    @37
    cA
    recn
    @0
    cA
    pncan3
    sylancr
    #
    fveq2d
    @3
    @18
    cc
    wcel
    #
    @44
    @19
    wceq
    @3
    @18
    @39
    recnd
    #
    @18
    sinhalfpip
    syl
    eqtr3d
    breq1d
    @3
    @9
    @22
    cc0
    clt
    @3
    @43
    ccos
    cfv
    #
    @9
    @22
    @3
    @43
    cA
    ccos
    @45
    fveq2d
    @3
    @46
    @48
    @22
    wceq
    @47
    @18
    coshalfpip
    syl
    eqtr3d
    breq1d
    anbi12d
    sylibrd
    3impib
    sylbi
end
