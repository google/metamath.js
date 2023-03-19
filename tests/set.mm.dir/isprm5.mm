include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "wn.mm"
include "isprm4.mm"
include "cmul.mm"
include "prmuz2.mm"
include "a1i.mm"
include "clt.mm"
include "c1.mm"
include "cn.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "cr.mm"
include "cc0.mm"
include "wb.mm"
include "eluzelre.mm"
include "eluz2nn.mm"
include "nngt0d.mm"
include "ltmulgt11.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "remulcld.mm"
include "ltnled.mm"
include "oveq12.mm"
include "anidms.mm"
include "breq1d.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "imim2d.mm"
include "con2.mm"
include "syl6.mm"
include "imim12d.mm"
include "ralimdv2.mm"
include "wrex.mm"
include "annim.mm"
include "weq.mm"
include "breq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "ancom2s.mm"
include "expr.mm"
include "ad2ant2lr.mm"
include "cdiv.mm"
include "cz.mm"
include "simprl.mm"
include "wne.mm"
include "eluzelz.mm"
include "ad2antlr.mm"
include "nnne0d.mm"
include "ad2antrr.mm"
include "dvdsval2.mm"
include "recnd.mm"
include "mulid2d.mm"
include "dvdsle.mm"
include "imp.mm"
include "syl21anc.mm"
include "simprr.mm"
include "neqned.mm"
include "necomd.mm"
include "ltlend.mm"
include "mpbir2and.mm"
include "eqbrtrd.mm"
include "1red.mm"
include "zred.mm"
include "nnre.mm"
include "nngt0.mm"
include "jca.mm"
include "syl.mm"
include "ltmuldiv.mm"
include "eluz2b1.mm"
include "sylanbrc.mm"
include "crp.mm"
include "nnmulcld.mm"
include "nnrp.mm"
include "rpdivcl.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "lemul1d.mm"
include "divmuldivd.mm"
include "nncnd.mm"
include "divassd.mm"
include "eqtrd.mm"
include "divcan2d.mm"
include "eqcomd.mm"
include "breq12d.mm"
include "bitr4d.mm"
include "biimpd.mm"
include "dvds0lem.mm"
include "syl31anc.mm"
include "jctird.mm"
include "syl6an.mm"
include "letrid.mm"
include "mpjaod.mm"
include "ex.mm"
include "syl5bir.mm"
include "rexlimdva.mm"
include "prmz.mm"
include "ad2antrl.mm"
include "ad3antlr.mm"
include "ad3antrrr.mm"
include "eluzge2nn0.mm"
include "nn0ge0d.mm"
include "nnnn0.mm"
include "le2msq.mm"
include "syl22anc.mm"
include "simplrl.mm"
include "letrd.mm"
include "simplrr.mm"
include "dvdstr.mm"
include "mp2and.mm"
include "jc.mm"
include "exprmfct.mm"
include "reximddv.mm"
include "syld.mm"
include "rexnal.mm"
include "3imtr3g.mm"
include "impcon4bid.mm"
include "prmnn.mm"
include "sqvald.mm"
include "imbi1d.mm"
include "ralbiia.mm"
include "syl6bbr.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isprm5
  let vz: setvar z
  let cP: class P
  let vx: setvar x

  disjoint P z
  disjoint x z
  disjoint P x
  assert |- ( P e. Prime <-> ( P e. ( ZZ>= ` 2 ) /\ A. z e. Prime ( ( z ^ 2 ) <_ P -> -. z || P ) ) )

  proof
    cP
    cprime
    wcel
    cP
    c2
    cuz
    cfv
    #
    wcel
    #
    vz
    cv
    #
    cP
    cdvds
    wbr
    #
    @2
    cP
    wceq
    #
    wi
    #
    vz
    @0
    wral
    #
    wa
    @1
    @2
    c2
    cexp
    co
    #
    cP
    cle
    wbr
    #
    @3
    wn
    #
    wi
    #
    vz
    cprime
    wral
    #
    wa
    vz
    cP
    isprm4
    @1
    @6
    @11
    @1
    @6
    @2
    @2
    cmul
    co
    #
    cP
    cle
    wbr
    #
    @9
    wi
    #
    vz
    cprime
    wral
    #
    @11
    @1
    @6
    @15
    @1
    @5
    @14
    vz
    @0
    cprime
    @1
    @2
    cprime
    wcel
    #
    @2
    @0
    wcel
    #
    @5
    @14
    @16
    @17
    wi
    @1
    @2
    prmuz2
    #
    a1i
    @1
    @5
    @3
    @13
    wn
    #
    wi
    @14
    @1
    @4
    @19
    @3
    @1
    @19
    @4
    cP
    cP
    cmul
    co
    #
    cP
    cle
    wbr
    #
    wn
    #
    @1
    cP
    @20
    clt
    wbr
    #
    @22
    @1
    c1
    cP
    clt
    wbr
    #
    @23
    @1
    cP
    cn
    wcel
    #
    @24
    cP
    eluz2b2
    simprbi
    @1
    cP
    cr
    wcel
    #
    @26
    cc0
    cP
    clt
    wbr
    @24
    @23
    wb
    c2
    cP
    eluzelre
    #
    @27
    @1
    cP
    cP
    eluz2nn
    #
    nngt0d
    cP
    cP
    ltmulgt11
    syl3anc
    mpbid
    @1
    cP
    @20
    @27
    @1
    cP
    cP
    @27
    @27
    remulcld
    ltnled
    mpbid
    @4
    @13
    @21
    @4
    @12
    @20
    cP
    cle
    @4
    @12
    @20
    wceq
    @2
    cP
    @2
    cP
    cmul
    oveq12
    anidms
    breq1d
    notbid
    syl5ibrcom
    imim2d
    @3
    @13
    con2
    syl6
    imim12d
    ralimdv2
    @1
    @5
    wn
    #
    vz
    @0
    wrex
    #
    @14
    wn
    #
    vz
    cprime
    wrex
    #
    @6
    wn
    @15
    wn
    @1
    @30
    vx
    cv
    #
    @33
    cmul
    co
    #
    cP
    cle
    wbr
    #
    @33
    cP
    cdvds
    wbr
    #
    wa
    #
    vx
    @0
    wrex
    #
    @32
    @1
    @29
    @38
    vz
    @0
    @29
    @3
    @4
    wn
    #
    wa
    #
    @1
    @17
    wa
    #
    @38
    @3
    @4
    annim
    @41
    @40
    @38
    @41
    @40
    wa
    #
    @13
    @38
    cP
    @12
    cle
    wbr
    #
    @17
    @3
    @13
    @38
    wi
    @1
    @39
    @17
    @3
    @13
    @38
    @17
    @13
    @3
    @38
    @37
    @13
    @3
    wa
    vx
    @2
    @0
    vx
    vz
    weq
    #
    @35
    @13
    @36
    @3
    @44
    @34
    @12
    cP
    cle
    @44
    @34
    @12
    wceq
    @33
    @2
    @33
    @2
    cmul
    oveq12
    anidms
    breq1d
    @33
    @2
    cP
    cdvds
    breq1
    anbi12d
    rspcev
    ancom2s
    expr
    ad2ant2lr
    @42
    cP
    @2
    cdiv
    co
    #
    @0
    wcel
    #
    @43
    @45
    @45
    cmul
    co
    #
    cP
    cle
    wbr
    #
    @45
    cP
    cdvds
    wbr
    #
    wa
    #
    @38
    @42
    @45
    cz
    wcel
    #
    c1
    @45
    clt
    wbr
    #
    @46
    @42
    @3
    @51
    @41
    @3
    @39
    simprl
    #
    @42
    @2
    cz
    wcel
    #
    @2
    cc0
    wne
    cP
    cz
    wcel
    #
    @3
    @51
    wb
    @17
    @54
    @1
    @40
    c2
    @2
    eluzelz
    ad2antlr
    #
    @42
    @2
    @17
    @2
    cn
    wcel
    #
    @1
    @40
    @2
    eluz2nn
    ad2antlr
    #
    nnne0d
    #
    @1
    @55
    @17
    @40
    c2
    cP
    eluzelz
    #
    ad2antrr
    #
    @2
    cP
    dvdsval2
    syl3anc
    mpbid
    #
    @42
    c1
    @2
    cmul
    co
    #
    cP
    clt
    wbr
    #
    @52
    @42
    @63
    @2
    cP
    clt
    @42
    @2
    @42
    @2
    @17
    @2
    cr
    wcel
    #
    @1
    @40
    c2
    @2
    eluzelre
    ad2antlr
    #
    recnd
    #
    mulid2d
    @42
    @2
    cP
    clt
    wbr
    @2
    cP
    cle
    wbr
    #
    cP
    @2
    wne
    @42
    @54
    @25
    @3
    @68
    @56
    @1
    @25
    @17
    @40
    @28
    ad2antrr
    #
    @53
    @54
    @25
    wa
    @3
    @68
    @2
    cP
    dvdsle
    imp
    syl21anc
    @42
    @2
    cP
    @42
    @2
    cP
    @41
    @3
    @39
    simprr
    neqned
    necomd
    @42
    @2
    cP
    @66
    @1
    @26
    @17
    @40
    @27
    ad2antrr
    #
    ltlend
    mpbir2and
    eqbrtrd
    @42
    c1
    cr
    wcel
    @26
    @65
    cc0
    @2
    clt
    wbr
    #
    wa
    #
    @64
    @52
    wb
    @42
    1red
    @42
    cP
    @61
    zred
    @42
    @57
    @72
    @58
    @57
    @65
    @71
    @2
    nnre
    @2
    nngt0
    jca
    syl
    c1
    cP
    @2
    ltmuldiv
    syl3anc
    mpbid
    @45
    eluz2b1
    sylanbrc
    @42
    @43
    @48
    @49
    @42
    @43
    @48
    @42
    @43
    cP
    cP
    @12
    cdiv
    co
    #
    cmul
    co
    #
    @12
    @73
    cmul
    co
    #
    cle
    wbr
    @48
    @42
    cP
    @12
    @73
    @70
    @42
    @2
    @2
    @66
    @66
    remulcld
    #
    @42
    @25
    @12
    cn
    wcel
    #
    @73
    crp
    wcel
    #
    @69
    @42
    @2
    @2
    @58
    @58
    nnmulcld
    #
    @25
    cP
    crp
    wcel
    @12
    crp
    wcel
    @78
    @77
    cP
    nnrp
    @12
    nnrp
    cP
    @12
    rpdivcl
    syl2an
    syl2anc
    lemul1d
    @42
    @47
    @74
    cP
    @75
    cle
    @42
    @47
    @20
    @12
    cdiv
    co
    @74
    @42
    cP
    @2
    cP
    @2
    @42
    cP
    @70
    recnd
    #
    @67
    @80
    @67
    @59
    @59
    divmuldivd
    @42
    cP
    cP
    @12
    @80
    @80
    @42
    @12
    @79
    nncnd
    #
    @42
    @12
    @79
    nnne0d
    #
    divassd
    eqtrd
    @42
    @75
    cP
    @42
    cP
    @12
    @80
    @81
    @82
    divcan2d
    eqcomd
    breq12d
    bitr4d
    biimpd
    @42
    @54
    @51
    @55
    @2
    @45
    cmul
    co
    cP
    wceq
    @49
    @56
    @62
    @61
    @42
    cP
    @2
    @80
    @67
    @59
    divcan2d
    @2
    @45
    cP
    dvds0lem
    syl31anc
    jctird
    @37
    @50
    vx
    @45
    @0
    @33
    @45
    wceq
    #
    @35
    @48
    @36
    @49
    @83
    @34
    @47
    cP
    cle
    @83
    @34
    @47
    wceq
    @33
    @45
    @33
    @45
    cmul
    oveq12
    anidms
    breq1d
    @33
    @45
    cP
    cdvds
    breq1
    anbi12d
    rspcev
    syl6an
    @42
    @12
    cP
    @76
    @70
    letrid
    mpjaod
    ex
    syl5bir
    rexlimdva
    @1
    @37
    @32
    vx
    @0
    @1
    @33
    @0
    wcel
    #
    wa
    #
    @37
    @32
    @85
    @37
    wa
    #
    @2
    @33
    cdvds
    wbr
    #
    @31
    vz
    cprime
    @86
    @16
    @87
    wa
    #
    wa
    #
    @13
    @3
    @89
    @12
    @34
    cP
    @89
    @2
    @2
    @89
    @2
    @16
    @54
    @86
    @87
    @2
    prmz
    ad2antrl
    #
    zred
    #
    @91
    remulcld
    @89
    @33
    @33
    @89
    @33
    @84
    @33
    cz
    wcel
    #
    @1
    @37
    @88
    c2
    @33
    eluzelz
    ad3antlr
    #
    zred
    #
    @94
    remulcld
    @89
    cP
    @1
    @55
    @84
    @37
    @88
    @60
    ad3antrrr
    #
    zred
    @89
    @2
    @33
    cle
    wbr
    #
    @12
    @34
    cle
    wbr
    #
    @89
    @54
    @33
    cn
    wcel
    #
    @87
    @96
    @90
    @84
    @98
    @1
    @37
    @88
    @33
    eluz2nn
    ad3antlr
    #
    @86
    @16
    @87
    simprr
    #
    @54
    @98
    wa
    @87
    @96
    @2
    @33
    dvdsle
    imp
    syl21anc
    @89
    @65
    cc0
    @2
    cle
    wbr
    #
    @33
    cr
    wcel
    cc0
    @33
    cle
    wbr
    #
    @96
    @97
    wb
    @91
    @16
    @101
    @86
    @87
    @16
    @17
    @101
    @18
    @17
    @2
    @2
    eluzge2nn0
    nn0ge0d
    syl
    ad2antrl
    @94
    @89
    @98
    @102
    @99
    @98
    @33
    @33
    nnnn0
    nn0ge0d
    syl
    @2
    @33
    le2msq
    syl22anc
    mpbid
    @85
    @35
    @36
    @88
    simplrl
    letrd
    @89
    @87
    @36
    @3
    @100
    @85
    @35
    @36
    @88
    simplrr
    @89
    @54
    @92
    @55
    @87
    @36
    wa
    @3
    wi
    @90
    @93
    @95
    @2
    @33
    cP
    dvdstr
    syl3anc
    mp2and
    jc
    @84
    @87
    vz
    cprime
    wrex
    @1
    @37
    @33
    vz
    exprmfct
    ad2antlr
    reximddv
    ex
    rexlimdva
    syld
    @5
    vz
    @0
    rexnal
    @14
    vz
    cprime
    rexnal
    3imtr3g
    impcon4bid
    @10
    @14
    vz
    cprime
    @16
    @8
    @13
    @9
    @16
    @7
    @12
    cP
    cle
    @16
    @2
    @16
    @2
    @2
    prmnn
    nncnd
    sqvald
    breq1d
    imbi1d
    ralbiia
    syl6bbr
    pm5.32i
    bitri
end
