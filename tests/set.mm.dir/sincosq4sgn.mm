include "c3.mm"
include "cpi.mm"
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
include "cxr.mm"
include "wb.mm"
include "3re.mm"
include "halfpire.mm"
include "remulcli.mm"
include "rexri.mm"
include "2re.mm"
include "pire.mm"
include "elioo2.mm"
include "mp2an.mm"
include "cmin.mm"
include "cneg.mm"
include "caddc.mm"
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
include "breq1i.mm"
include "ltaddsub.mm"
include "mp3an12.mm"
include "syl5bbr.mm"
include "ltsubadd.mm"
include "mp3an23.mm"
include "c4.mm"
include "df-4.mm"
include "oveq2i.mm"
include "cc.mm"
include "wne.mm"
include "wceq.mm"
include "4cn.mm"
include "2cnne0.mm"
include "div12.mm"
include "mp3an.mm"
include "4d2e2.mm"
include "mulcomi.mm"
include "eqtri.mm"
include "breq2i.mm"
include "syl6rbb.mm"
include "anbi12d.mm"
include "resubcl.mm"
include "mpan2.mm"
include "sincosq3sgn.mm"
include "sylbir.mm"
include "syl3an1.mm"
include "3expib.mm"
include "sylbid.mm"
include "resincld.mm"
include "lt0neg1d.mm"
include "anbi1d.mm"
include "sylibd.mm"
include "recn.mm"
include "pncan3.mm"
include "sylancr.mm"
include "fveq2d.mm"
include "recnd.mm"
include "coshalfpip.mm"
include "syl.mm"
include "eqtr3d.mm"
include "breq2d.mm"
include "sinhalfpip.mm"
include "breq1d.mm"
include "sylibrd.mm"
include "3impib.mm"
include "ancomd.mm"
include "sylbi.mm"

theorem sincosq4sgn
  let cA: class A


  assert |- ( A e. ( ( 3 x. ( _pi / 2 ) ) (,) ( 2 x. _pi ) ) -> ( ( sin ` A ) < 0 /\ 0 < ( cos ` A ) ) )

  proof
    cA
    c3
    cpi
    c2
    cdiv
    co
    #
    cmul
    co
    #
    c2
    cpi
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
    @1
    cA
    clt
    wbr
    #
    cA
    @2
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
    cc0
    cA
    ccos
    cfv
    #
    clt
    wbr
    #
    wa
    @1
    cxr
    wcel
    #
    @2
    cxr
    wcel
    @3
    @7
    wb
    @1
    c3
    @0
    3re
    halfpire
    remulcli
    #
    rexri
    #
    @2
    c2
    cpi
    2re
    pire
    remulcli
    rexri
    @1
    @2
    cA
    elioo2
    mp2an
    @7
    @11
    @9
    @4
    @5
    @6
    @11
    @9
    wa
    #
    @4
    @5
    @6
    wa
    #
    cc0
    cA
    @0
    cmin
    co
    #
    csin
    cfv
    #
    cneg
    #
    clt
    wbr
    #
    @17
    ccos
    cfv
    #
    cc0
    clt
    wbr
    #
    wa
    #
    @15
    @4
    @16
    @18
    cc0
    clt
    wbr
    #
    @22
    wa
    #
    @23
    @4
    @16
    cpi
    @17
    clt
    wbr
    #
    @17
    @1
    clt
    wbr
    #
    wa
    @25
    @4
    @5
    @26
    @6
    @27
    @5
    cpi
    @0
    caddc
    co
    #
    cA
    clt
    wbr
    #
    @4
    @26
    @28
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
    @28
    c3
    @30
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
    @31
    cpi
    @32
    @0
    caddc
    cpi
    c2
    cpi
    pire
    recni
    #
    2cn
    2ne0
    divcan2i
    @0
    @33
    mulid2i
    #
    oveq12i
    3eqtrri
    breq1i
    cpi
    cr
    wcel
    @0
    cr
    wcel
    #
    @4
    @29
    @26
    wb
    pire
    halfpire
    cpi
    @0
    cA
    ltaddsub
    mp3an12
    syl5bbr
    @4
    @27
    cA
    @1
    @0
    caddc
    co
    #
    clt
    wbr
    #
    @6
    @4
    @36
    @1
    cr
    wcel
    @27
    @38
    wb
    halfpire
    @13
    cA
    @0
    @1
    ltsubadd
    mp3an23
    @37
    @2
    cA
    clt
    @37
    c4
    @0
    cmul
    co
    #
    @2
    @39
    c3
    c1
    caddc
    co
    #
    @0
    cmul
    co
    @1
    @32
    caddc
    co
    @37
    c4
    @40
    @0
    cmul
    df-4
    oveq1i
    c3
    c1
    @0
    c3
    3re
    recni
    ax-1cn
    @33
    adddiri
    @32
    @0
    @1
    caddc
    @35
    oveq2i
    3eqtrri
    @39
    cpi
    c4
    c2
    cdiv
    co
    #
    cmul
    co
    #
    @2
    c4
    cc
    wcel
    cpi
    cc
    wcel
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    @39
    @42
    wceq
    4cn
    @34
    2cnne0
    c4
    cpi
    c2
    div12
    mp3an
    @42
    cpi
    c2
    cmul
    co
    @2
    @41
    c2
    cpi
    cmul
    4d2e2
    oveq2i
    cpi
    c2
    @34
    2cn
    mulcomi
    eqtri
    eqtri
    eqtri
    breq2i
    syl6rbb
    anbi12d
    @4
    @26
    @27
    @25
    @4
    @17
    cr
    wcel
    #
    @26
    @27
    @25
    @4
    @36
    @43
    halfpire
    cA
    @0
    resubcl
    mpan2
    #
    @43
    @26
    @27
    w3a
    #
    @17
    cpi
    @1
    cioo
    co
    wcel
    #
    @25
    cpi
    cxr
    wcel
    @12
    @46
    @45
    wb
    cpi
    pire
    rexri
    @14
    cpi
    @1
    @17
    elioo2
    mp2an
    @17
    sincosq3sgn
    sylbir
    syl3an1
    3expib
    sylbid
    @4
    @24
    @20
    @22
    @4
    @18
    @4
    @17
    @44
    resincld
    lt0neg1d
    anbi1d
    sylibd
    @4
    @11
    @20
    @9
    @22
    @4
    @10
    @19
    cc0
    clt
    @4
    @0
    @17
    caddc
    co
    #
    ccos
    cfv
    #
    @10
    @19
    @4
    @47
    cA
    ccos
    @4
    @0
    cc
    wcel
    cA
    cc
    wcel
    @47
    cA
    wceq
    @33
    cA
    recn
    @0
    cA
    pncan3
    sylancr
    #
    fveq2d
    @4
    @17
    cc
    wcel
    #
    @48
    @19
    wceq
    @4
    @17
    @44
    recnd
    #
    @17
    coshalfpip
    syl
    eqtr3d
    breq2d
    @4
    @8
    @21
    cc0
    clt
    @4
    @47
    csin
    cfv
    #
    @8
    @21
    @4
    @47
    cA
    csin
    @49
    fveq2d
    @4
    @50
    @52
    @21
    wceq
    @51
    @17
    sinhalfpip
    syl
    eqtr3d
    breq1d
    anbi12d
    sylibrd
    3impib
    ancomd
    sylbi
end
