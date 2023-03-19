include "cc0.mm"
include "c1.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cmin.mm"
include "cabs.mm"
include "c6.mm"
include "clt.mm"
include "wbr.mm"
include "c3.mm"
include "cmul.mm"
include "wa.mm"
include "c4.mm"
include "cuz.mm"
include "cv.mm"
include "cn0.mm"
include "ci.mm"
include "cfa.mm"
include "cmpt.mm"
include "csu.mm"
include "cre.mm"
include "wceq.mm"
include "caddc.mm"
include "cr.mm"
include "cle.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "1re.mm"
include "elioc2.mm"
include "mp2an.mm"
include "simp1bi.mm"
include "eqid.mm"
include "recos4p.mm"
include "syl.mm"
include "eqcomd.mm"
include "recoscld.mm"
include "recnd.mm"
include "resqcld.mm"
include "rehalfcld.mm"
include "resubcl.mm"
include "sylancr.mm"
include "cc.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "4nn0.mm"
include "eftlcl.mm"
include "sylancl.mm"
include "recld.mm"
include "subaddd.mm"
include "mpbird.mm"
include "fveq2d.mm"
include "abscld.mm"
include "cn.mm"
include "6nn.mm"
include "nndivre.mm"
include "absrele.mm"
include "reexpcl.mm"
include "ef01bndlem.mm"
include "2nn0.mm"
include "a1i.mm"
include "cz.mm"
include "4z.mm"
include "2re.mm"
include "4re.mm"
include "2lt4.mm"
include "ltleii.mm"
include "2z.mm"
include "eluz1i.mm"
include "mpbir2an.mm"
include "simp2bi.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "mpd.mm"
include "simp3bi.mm"
include "leexp2rd.mm"
include "6re.mm"
include "6pos.mm"
include "lediv1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "ltletrd.mm"
include "lelttrd.mm"
include "eqbrtrd.mm"
include "absdifltd.mm"
include "1cnd.mm"
include "subsub4d.mm"
include "halfpm6th.mm"
include "simpri.mm"
include "oveq2i.mm"
include "2cn.mm"
include "2ne0.mm"
include "reccli.mm"
include "6cn.mm"
include "nnne0i.mm"
include "adddi.mm"
include "mp3an23.mm"
include "syl5eqr.mm"
include "wne.mm"
include "3cn.mm"
include "3ne0.mm"
include "pm3.2i.mm"
include "div12.mm"
include "mp3an13.mm"
include "divrec.mm"
include "oveq12d.mm"
include "3eqtr4rd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "subsubd.mm"
include "simpli.mm"
include "subdi.mm"
include "eqtr3d.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "bitrd.mm"

theorem cos01bnd
  let cA: class A
  let vk: setvar k
  let vn: setvar n


  assert |- ( A e. ( 0 (,] 1 ) -> ( ( 1 - ( 2 x. ( ( A ^ 2 ) / 3 ) ) ) < ( cos ` A ) /\ ( cos ` A ) < ( 1 - ( ( A ^ 2 ) / 3 ) ) ) )

  proof
    cA
    cc0
    c1
    cioc
    co
    wcel
    #
    cA
    ccos
    cfv
    #
    c1
    cA
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @2
    c6
    cdiv
    co
    #
    clt
    wbr
    #
    c1
    c2
    @2
    c3
    cdiv
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @1
    clt
    wbr
    #
    @1
    c1
    @9
    cmin
    co
    #
    clt
    wbr
    #
    wa
    #
    @0
    @6
    c4
    cuz
    cfv
    vk
    cv
    vn
    cn0
    ci
    cA
    cmul
    co
    #
    vn
    cv
    #
    cexp
    co
    @17
    cfa
    cfv
    cdiv
    co
    cmpt
    #
    cfv
    vk
    csu
    #
    cre
    cfv
    #
    cabs
    cfv
    #
    @7
    clt
    @0
    @5
    @20
    cabs
    @0
    @5
    @20
    wceq
    @4
    @20
    caddc
    co
    #
    @1
    wceq
    @0
    @1
    @22
    @0
    cA
    cr
    wcel
    #
    @1
    @22
    wceq
    @0
    @23
    cc0
    cA
    clt
    wbr
    #
    cA
    c1
    cle
    wbr
    #
    cc0
    cxr
    wcel
    c1
    cr
    wcel
    #
    @0
    @23
    @24
    @25
    w3a
    wb
    0xr
    1re
    cc0
    c1
    cA
    elioc2
    mp2an
    #
    simp1bi
    #
    cA
    vk
    vn
    @18
    @18
    eqid
    #
    recos4p
    syl
    eqcomd
    @0
    @1
    @4
    @20
    @0
    @1
    @0
    cA
    @28
    recoscld
    #
    recnd
    @0
    @4
    @0
    @26
    @3
    cr
    wcel
    @4
    cr
    wcel
    1re
    @0
    @2
    @0
    cA
    @28
    resqcld
    #
    rehalfcld
    #
    c1
    @3
    resubcl
    sylancr
    #
    recnd
    @0
    @20
    @0
    @19
    @0
    @16
    cc
    wcel
    #
    c4
    cn0
    wcel
    #
    @19
    cc
    wcel
    #
    @0
    ci
    cc
    wcel
    cA
    cc
    wcel
    @34
    ax-icn
    @0
    cA
    @28
    recnd
    ci
    cA
    mulcl
    sylancr
    4nn0
    @16
    vk
    vn
    @18
    c4
    @29
    eftlcl
    sylancl
    #
    recld
    recnd
    #
    subaddd
    mpbird
    fveq2d
    @0
    @21
    @19
    cabs
    cfv
    #
    @7
    @0
    @20
    @38
    abscld
    @0
    @19
    @37
    abscld
    #
    @0
    @2
    cr
    wcel
    #
    c6
    cn
    wcel
    #
    @7
    cr
    wcel
    @31
    6nn
    @2
    c6
    nndivre
    sylancl
    #
    @0
    @36
    @21
    @39
    cle
    wbr
    @37
    @19
    absrele
    syl
    @0
    @39
    cA
    c4
    cexp
    co
    #
    c6
    cdiv
    co
    #
    @7
    @40
    @0
    @44
    cr
    wcel
    #
    @42
    @45
    cr
    wcel
    @0
    @23
    @35
    @46
    @28
    4nn0
    cA
    c4
    reexpcl
    sylancl
    #
    6nn
    @44
    c6
    nndivre
    sylancl
    @43
    cA
    vk
    vn
    @18
    @29
    ef01bndlem
    @0
    @44
    @2
    cle
    wbr
    #
    @45
    @7
    cle
    wbr
    #
    @0
    cA
    c2
    c4
    @28
    c2
    cn0
    wcel
    @0
    2nn0
    a1i
    c4
    c2
    cuz
    cfv
    wcel
    #
    @0
    @50
    c4
    cz
    wcel
    c2
    c4
    cle
    wbr
    4z
    c2
    c4
    2re
    4re
    2lt4
    ltleii
    c2
    c4
    2z
    eluz1i
    mpbir2an
    a1i
    @0
    @24
    cc0
    cA
    cle
    wbr
    #
    @0
    @23
    @24
    @25
    @27
    simp2bi
    @0
    cc0
    cr
    wcel
    @23
    @24
    @51
    wi
    0re
    @28
    cc0
    cA
    ltle
    sylancr
    mpd
    @0
    @23
    @24
    @25
    @27
    simp3bi
    leexp2rd
    @0
    @46
    @41
    c6
    cr
    wcel
    #
    cc0
    c6
    clt
    wbr
    #
    @48
    @49
    wb
    @47
    @31
    @52
    @0
    6re
    a1i
    @53
    @0
    6pos
    a1i
    @44
    @2
    c6
    lediv1
    syl112anc
    mpbid
    ltletrd
    lelttrd
    eqbrtrd
    @0
    @8
    @4
    @7
    cmin
    co
    #
    @1
    clt
    wbr
    #
    @1
    @4
    @7
    caddc
    co
    #
    clt
    wbr
    #
    wa
    @15
    @0
    @1
    @4
    @7
    @30
    @33
    @43
    absdifltd
    @0
    @55
    @12
    @57
    @14
    @0
    @54
    @11
    @1
    clt
    @0
    @54
    c1
    @3
    @7
    caddc
    co
    #
    cmin
    co
    @11
    @0
    c1
    @3
    @7
    @0
    1cnd
    #
    @0
    @3
    @32
    recnd
    #
    @0
    @7
    @43
    recnd
    #
    subsub4d
    @0
    @58
    @10
    c1
    cmin
    @0
    @2
    c2
    c3
    cdiv
    co
    #
    cmul
    co
    #
    @2
    c1
    c2
    cdiv
    co
    #
    cmul
    co
    #
    @2
    c1
    c6
    cdiv
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @10
    @58
    @0
    @63
    @2
    @64
    @66
    caddc
    co
    #
    cmul
    co
    #
    @68
    @69
    @62
    @2
    cmul
    @64
    @66
    cmin
    co
    #
    c1
    c3
    cdiv
    co
    #
    wceq
    #
    @69
    @62
    wceq
    #
    halfpm6th
    simpri
    oveq2i
    @0
    @2
    cc
    wcel
    #
    @70
    @68
    wceq
    #
    @0
    @2
    @31
    recnd
    #
    @75
    @64
    cc
    wcel
    #
    @66
    cc
    wcel
    #
    @76
    c2
    2cn
    2ne0
    reccli
    #
    c6
    6cn
    c6
    6nn
    nnne0i
    #
    reccli
    #
    @2
    @64
    @66
    adddi
    mp3an23
    syl
    syl5eqr
    @0
    @75
    @10
    @63
    wceq
    #
    @77
    c2
    cc
    wcel
    #
    @75
    c3
    cc
    wcel
    #
    c3
    cc0
    wne
    #
    wa
    @83
    2cn
    @85
    @86
    3cn
    3ne0
    pm3.2i
    c2
    @2
    c3
    div12
    mp3an13
    syl
    @0
    @3
    @65
    @7
    @67
    caddc
    @0
    @75
    @3
    @65
    wceq
    #
    @77
    @75
    @84
    c2
    cc0
    wne
    @87
    2cn
    2ne0
    @2
    c2
    divrec
    mp3an23
    syl
    #
    @0
    @75
    @7
    @67
    wceq
    #
    @77
    @75
    c6
    cc
    wcel
    c6
    cc0
    wne
    @89
    6cn
    @81
    @2
    c6
    divrec
    mp3an23
    syl
    #
    oveq12d
    3eqtr4rd
    oveq2d
    eqtrd
    breq1d
    @0
    @56
    @13
    @1
    clt
    @0
    c1
    @3
    @7
    cmin
    co
    #
    cmin
    co
    @56
    @13
    @0
    c1
    @3
    @7
    @59
    @60
    @61
    subsubd
    @0
    @91
    @9
    c1
    cmin
    @0
    @2
    @72
    cmul
    co
    #
    @65
    @67
    cmin
    co
    #
    @9
    @91
    @0
    @92
    @2
    @71
    cmul
    co
    #
    @93
    @71
    @72
    @2
    cmul
    @73
    @74
    halfpm6th
    simpli
    oveq2i
    @0
    @75
    @94
    @93
    wceq
    #
    @77
    @75
    @78
    @79
    @95
    @80
    @82
    @2
    @64
    @66
    subdi
    mp3an23
    syl
    syl5eqr
    @0
    @75
    @9
    @92
    wceq
    #
    @77
    @75
    @85
    @86
    @96
    3cn
    3ne0
    @2
    c3
    divrec
    mp3an23
    syl
    @0
    @3
    @65
    @7
    @67
    cmin
    @88
    @90
    oveq12d
    3eqtr4rd
    oveq2d
    eqtr3d
    breq2d
    anbi12d
    bitrd
    mpbid
end
