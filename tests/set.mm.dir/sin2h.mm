include "cc0.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "cicc.mm"
include "wcel.mm"
include "cdiv.mm"
include "csin.mm"
include "cfv.mm"
include "c1.mm"
include "ccos.mm"
include "cmin.mm"
include "csqrt.mm"
include "cr.mm"
include "wss.mm"
include "0re.mm"
include "2re.mm"
include "pire.mm"
include "remulcli.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sseli.mm"
include "rehalfcld.mm"
include "resincld.mm"
include "1re.mm"
include "recoscl.mm"
include "resubcl.mm"
include "sylancr.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "cosbnd.mm"
include "simprd.mm"
include "wb.mm"
include "subge0.mm"
include "halfnneg2.mm"
include "syl.mm"
include "bitr3d.mm"
include "mpbid.mm"
include "resqrtcld.mm"
include "w3a.mm"
include "elicc2i.mm"
include "wa.mm"
include "clt.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ledivmul.mm"
include "mp3an23.mm"
include "bicomd.mm"
include "anbi12d.mm"
include "cxr.mm"
include "rehalfcl.mm"
include "rexrd.mm"
include "0xr.mm"
include "rexri.mm"
include "elicc4.mm"
include "mp3an12.mm"
include "bitr4d.mm"
include "biimpd.mm"
include "3impib.mm"
include "sylbi.mm"
include "sinq12ge0.mm"
include "sqrtge0d.mm"
include "cc.mm"
include "cexp.mm"
include "wceq.mm"
include "recnd.mm"
include "ax-1cn.mm"
include "coscl.mm"
include "subcl.mm"
include "halfcld.mm"
include "sqsqrtd.mm"
include "halfcl.mm"
include "caddc.mm"
include "sqcld.mm"
include "2cn.mm"
include "mulcom.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "mulid2i.mm"
include "df-2.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "subdir.mm"
include "mp3an13.mm"
include "mulcl.mm"
include "subsub3.mm"
include "3eqtr4d.mm"
include "sincl.mm"
include "pncand.mm"
include "sincossq.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "cos2t.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan2.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "sincld.mm"
include "divcan4.mm"
include "3eqtr2rd.mm"
include "sq11d.mm"

theorem sin2h
  let cA: class A


  assert |- ( A e. ( 0 [,] ( 2 x. _pi ) ) -> ( sin ` ( A / 2 ) ) = ( sqrt ` ( ( 1 - ( cos ` A ) ) / 2 ) ) )

  proof
    cA
    cc0
    c2
    cpi
    cmul
    co
    #
    cicc
    co
    #
    wcel
    #
    cA
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    c1
    cA
    ccos
    cfv
    #
    cmin
    co
    #
    c2
    cdiv
    co
    #
    csqrt
    cfv
    #
    @2
    @3
    @2
    cA
    @1
    cr
    cA
    cc0
    cr
    wcel
    @0
    cr
    wcel
    @1
    cr
    wss
    0re
    c2
    cpi
    2re
    pire
    remulcli
    #
    cc0
    @0
    iccssre
    mp2an
    sseli
    #
    rehalfcld
    resincld
    @2
    cA
    cr
    wcel
    #
    @8
    cr
    wcel
    @10
    @11
    @7
    @11
    @6
    @11
    c1
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    1re
    cA
    recoscl
    #
    c1
    @5
    resubcl
    sylancr
    #
    rehalfcld
    #
    @11
    @5
    c1
    cle
    wbr
    #
    cc0
    @7
    cle
    wbr
    #
    @11
    c1
    cneg
    @5
    cle
    wbr
    @18
    cA
    cosbnd
    simprd
    @11
    cc0
    @6
    cle
    wbr
    #
    @18
    @19
    @11
    @12
    @13
    @20
    @18
    wb
    1re
    @15
    c1
    @5
    subge0
    sylancr
    @11
    @14
    @20
    @19
    wb
    @16
    @6
    halfnneg2
    syl
    bitr3d
    mpbid
    #
    resqrtcld
    syl
    @2
    @3
    cc0
    cpi
    cicc
    co
    wcel
    #
    cc0
    @4
    cle
    wbr
    @2
    @11
    cc0
    cA
    cle
    wbr
    #
    cA
    @0
    cle
    wbr
    #
    w3a
    @22
    cc0
    @0
    cA
    0re
    @9
    elicc2i
    @11
    @23
    @24
    @22
    @11
    @23
    @24
    wa
    #
    @22
    @11
    @25
    cc0
    @3
    cle
    wbr
    #
    @3
    cpi
    cle
    wbr
    #
    wa
    #
    @22
    @11
    @23
    @26
    @24
    @27
    cA
    halfnneg2
    @11
    @27
    @24
    @11
    cpi
    cr
    wcel
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    @27
    @24
    wb
    pire
    @29
    @30
    2re
    2pos
    pm3.2i
    cA
    cpi
    c2
    ledivmul
    mp3an23
    bicomd
    anbi12d
    @11
    @3
    cxr
    wcel
    #
    @22
    @28
    wb
    #
    @11
    @3
    cA
    rehalfcl
    rexrd
    cc0
    cxr
    wcel
    cpi
    cxr
    wcel
    @31
    @32
    0xr
    cpi
    pire
    rexri
    cc0
    cpi
    @3
    elicc4
    mp3an12
    syl
    bitr4d
    biimpd
    3impib
    sylbi
    @3
    sinq12ge0
    syl
    @2
    @11
    cc0
    @8
    cle
    wbr
    @10
    @11
    @7
    @17
    @21
    sqrtge0d
    syl
    @2
    cA
    cc
    wcel
    #
    @4
    c2
    cexp
    co
    #
    @8
    c2
    cexp
    co
    #
    wceq
    @2
    cA
    @10
    recnd
    @33
    @35
    @7
    @34
    c2
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @34
    @33
    @7
    @33
    @6
    @33
    c1
    cc
    wcel
    #
    @5
    cc
    wcel
    @6
    cc
    wcel
    ax-1cn
    cA
    coscl
    c1
    @5
    subcl
    sylancr
    halfcld
    sqsqrtd
    @33
    @36
    @6
    c2
    cdiv
    @33
    @36
    c1
    c2
    @3
    cmul
    co
    #
    ccos
    cfv
    #
    cmin
    co
    #
    @6
    @33
    @3
    cc
    wcel
    #
    @36
    @41
    wceq
    cA
    halfcl
    #
    @42
    c1
    @3
    ccos
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    c2
    cmul
    co
    #
    c1
    c2
    @45
    cmul
    co
    #
    c1
    cmin
    co
    #
    cmin
    co
    #
    @36
    @41
    @42
    c1
    c2
    cmul
    co
    #
    @45
    c2
    cmul
    co
    #
    cmin
    co
    #
    c1
    c1
    caddc
    co
    #
    @48
    cmin
    co
    #
    @47
    @50
    @42
    @53
    @51
    @48
    cmin
    co
    @55
    @42
    @52
    @48
    @51
    cmin
    @42
    @45
    cc
    wcel
    #
    c2
    cc
    wcel
    #
    @52
    @48
    wceq
    @42
    @44
    @3
    coscl
    sqcld
    #
    2cn
    @45
    c2
    mulcom
    sylancl
    oveq2d
    @51
    @54
    @48
    cmin
    @51
    c2
    @54
    c2
    2cn
    mulid2i
    df-2
    eqtri
    oveq1i
    syl6eq
    @42
    @56
    @47
    @53
    wceq
    #
    @58
    @38
    @56
    @57
    @59
    ax-1cn
    2cn
    c1
    @45
    c2
    subdir
    mp3an13
    syl
    @42
    @48
    cc
    wcel
    #
    @50
    @55
    wceq
    #
    @42
    @57
    @56
    @60
    2cn
    @58
    c2
    @45
    mulcl
    sylancr
    @38
    @60
    @38
    @61
    ax-1cn
    ax-1cn
    c1
    @48
    c1
    subsub3
    mp3an13
    syl
    3eqtr4d
    @42
    @34
    @46
    c2
    cmul
    @42
    @34
    @45
    caddc
    co
    #
    @45
    cmin
    co
    @34
    @46
    @42
    @34
    @45
    @42
    @4
    @3
    sincl
    sqcld
    @58
    pncand
    @42
    @62
    c1
    @45
    cmin
    @3
    sincossq
    oveq1d
    eqtr3d
    oveq1d
    @42
    @40
    @49
    c1
    cmin
    @3
    cos2t
    oveq2d
    3eqtr4d
    syl
    @33
    @40
    @5
    c1
    cmin
    @33
    @39
    cA
    ccos
    @33
    @57
    c2
    cc0
    wne
    #
    @39
    cA
    wceq
    2cn
    2ne0
    cA
    c2
    divcan2
    mp3an23
    fveq2d
    oveq2d
    eqtrd
    oveq1d
    @33
    @34
    cc
    wcel
    #
    @37
    @34
    wceq
    #
    @33
    @4
    @33
    @3
    @43
    sincld
    sqcld
    @64
    @57
    @63
    @65
    2cn
    2ne0
    @34
    c2
    divcan4
    mp3an23
    syl
    3eqtr2rd
    syl
    sq11d
end
