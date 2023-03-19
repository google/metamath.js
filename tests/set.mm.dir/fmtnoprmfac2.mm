include "c2.mm"
include "wceq.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cprime.mm"
include "cfmtno.mm"
include "cdvds.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "c1.mm"
include "cn.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "wb.mm"
include "breq1.mm"
include "adantr.mm"
include "wn.mm"
include "cn0.mm"
include "eluzge2nn0.mm"
include "fmtnoodd.mm"
include "syl.mm"
include "adantl.mm"
include "pm2.21d.mm"
include "sylbid.mm"
include "a1d.mm"
include "ex.mm"
include "3impd.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmo.mm"
include "csn.mm"
include "cdif.mm"
include "simpr1.mm"
include "wne.mm"
include "neqne.mm"
include "anim2i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "3ad2ant2.mm"
include "impcom.mm"
include "simpr3.mm"
include "fmtnoprmfac2lem1.mm"
include "syl3anc.mm"
include "cz.mm"
include "simpl.mm"
include "2nn.mm"
include "a1i.mm"
include "oddprm.mm"
include "nnnn0d.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "jca.mm"
include "modprm1div.mm"
include "codz.mm"
include "cgcd.mm"
include "prmnn.mm"
include "2z.mm"
include "necomd.mm"
include "2prm.mm"
include "ancomd.mm"
include "prmrp.mm"
include "mpbird.mm"
include "3jca.mm"
include "odzdvds.mm"
include "eluz2nn.mm"
include "3ad2ant1.mm"
include "fmtnoprmfac1lem.mm"
include "peano2nn.mm"
include "nndivides.mm"
include "syl2an.mm"
include "eqcom.mm"
include "cc.mm"
include "cc0.mm"
include "nncnd.mm"
include "peano2cnm.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "nnmulcld.mm"
include "2cnne0.mm"
include "divmul3.mm"
include "nncn.mm"
include "2cnd.mm"
include "mulassd.mm"
include "expp1d.mm"
include "add1p1.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "1cnd.mm"
include "id.mm"
include "nnaddcld.mm"
include "mulcld.mm"
include "subadd2d.mm"
include "3bitrd.mm"
include "rexbidva.mm"
include "biimpd.mm"
include "adantrr.mm"
include "expr.mm"
include "3adant3.mm"
include "mpd.mm"
include "pm2.61i.mm"

theorem fmtnoprmfac2
  let cP: class P
  let vk: setvar k
  let cN: class N
  let vx: setvar x

  disjoint N k
  disjoint P k
  disjoint k x
  assert |- ( ( N e. ( ZZ>= ` 2 ) /\ P e. Prime /\ P || ( FermatNo ` N ) ) -> E. k e. NN P = ( ( k x. ( 2 ^ ( N + 2 ) ) ) + 1 ) )

  proof
    cP
    c2
    wceq
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    cP
    cprime
    wcel
    #
    cP
    cN
    cfmtno
    cfv
    #
    cdvds
    wbr
    #
    w3a
    #
    cP
    vk
    cv
    #
    c2
    cN
    c2
    caddc
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vk
    cn
    wrex
    #
    wi
    @0
    @1
    @2
    @4
    @12
    @0
    @1
    @2
    @4
    @12
    wi
    #
    wi
    @0
    @1
    wa
    #
    @13
    @2
    @14
    @4
    c2
    @3
    cdvds
    wbr
    #
    @12
    @0
    @4
    @15
    wb
    @1
    cP
    c2
    @3
    cdvds
    breq1
    adantr
    @14
    @15
    @12
    @1
    @15
    wn
    #
    @0
    @1
    cN
    cn0
    wcel
    @16
    cN
    eluzge2nn0
    cN
    fmtnoodd
    syl
    adantl
    pm2.21d
    sylbid
    a1d
    ex
    3impd
    @0
    wn
    #
    @5
    @12
    @17
    @5
    wa
    #
    c2
    cP
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cexp
    co
    #
    cP
    cmo
    co
    c1
    wceq
    #
    @12
    @18
    @1
    cP
    cprime
    c2
    csn
    cdif
    wcel
    #
    @4
    @22
    @17
    @1
    @2
    @4
    simpr1
    @5
    @17
    @23
    @2
    @1
    @17
    @23
    wi
    @4
    @2
    @17
    @23
    @2
    @17
    wa
    #
    @2
    cP
    c2
    wne
    #
    wa
    @23
    @17
    @25
    @2
    cP
    c2
    neqne
    #
    anim2i
    cP
    cprime
    c2
    eldifsn
    sylibr
    #
    ex
    3ad2ant2
    impcom
    #
    @17
    @1
    @2
    @4
    simpr3
    #
    cP
    cN
    fmtnoprmfac2lem1
    syl3anc
    @18
    @22
    cP
    @21
    c1
    cmin
    co
    cdvds
    wbr
    #
    @12
    @18
    @2
    @21
    cz
    wcel
    #
    wa
    #
    @22
    @30
    wb
    @5
    @17
    @32
    @2
    @1
    @17
    @32
    wi
    @4
    @2
    @17
    @32
    @24
    @2
    @31
    @2
    @17
    simpl
    @24
    @21
    @24
    c2
    @20
    c2
    cn
    wcel
    #
    @24
    2nn
    a1i
    @24
    @20
    @24
    @23
    @20
    cn
    wcel
    #
    @27
    cP
    oddprm
    syl
    #
    nnnn0d
    #
    nnexpcld
    nnzd
    jca
    ex
    3ad2ant2
    impcom
    @21
    cP
    modprm1div
    syl
    @18
    @30
    c2
    cP
    codz
    cfv
    cfv
    #
    @20
    cdvds
    wbr
    #
    @12
    @18
    cP
    cn
    wcel
    #
    c2
    cz
    wcel
    #
    c2
    cP
    cgcd
    co
    c1
    wceq
    #
    w3a
    #
    @20
    cn0
    wcel
    #
    wa
    #
    @30
    @38
    wb
    @5
    @17
    @44
    @2
    @1
    @17
    @44
    wi
    @4
    @2
    @17
    @44
    @24
    @42
    @43
    @24
    @39
    @40
    @41
    @2
    @39
    @17
    cP
    prmnn
    #
    adantr
    @40
    @24
    2z
    a1i
    @24
    @41
    c2
    cP
    wne
    #
    @17
    @46
    @2
    @17
    cP
    c2
    @26
    necomd
    adantl
    @24
    c2
    cprime
    wcel
    #
    @2
    wa
    @41
    @46
    wb
    @24
    @2
    @47
    @17
    @47
    @2
    @47
    @17
    2prm
    a1i
    anim2i
    ancomd
    c2
    cP
    prmrp
    syl
    mpbird
    3jca
    @36
    jca
    ex
    3ad2ant2
    impcom
    c2
    @20
    cP
    odzdvds
    syl
    @18
    @37
    c2
    cN
    c1
    caddc
    co
    #
    cexp
    co
    #
    wceq
    #
    @38
    @12
    wi
    #
    @18
    cN
    cn
    wcel
    #
    @23
    @4
    @50
    @5
    @52
    @17
    @1
    @2
    @52
    @4
    cN
    eluz2nn
    #
    3ad2ant1
    adantl
    @28
    @29
    cP
    cN
    fmtnoprmfac1lem
    syl3anc
    @18
    @50
    @51
    @18
    @50
    wa
    @38
    @49
    @20
    cdvds
    wbr
    #
    @12
    @50
    @38
    @54
    wb
    @18
    @37
    @49
    @20
    cdvds
    breq1
    adantl
    @18
    @54
    @12
    wi
    #
    @50
    @5
    @17
    @55
    @1
    @2
    @17
    @55
    wi
    @4
    @1
    @2
    @17
    @55
    @1
    @24
    wa
    @54
    @6
    @49
    cmul
    co
    #
    @20
    wceq
    #
    vk
    cn
    wrex
    #
    @12
    @1
    @49
    cn
    wcel
    #
    @34
    @54
    @58
    wb
    @24
    @1
    c2
    @48
    @33
    @1
    2nn
    a1i
    #
    @1
    @48
    @1
    @52
    @48
    cn
    wcel
    @53
    cN
    peano2nn
    #
    syl
    nnnn0d
    nnexpcld
    #
    @35
    vk
    @49
    @20
    nndivides
    syl2an
    @1
    @2
    @58
    @12
    wi
    @17
    @1
    @2
    wa
    #
    @58
    @12
    @63
    @57
    @11
    vk
    cn
    @63
    @6
    cn
    wcel
    #
    wa
    #
    @57
    @20
    @56
    wceq
    #
    @19
    @56
    c2
    cmul
    co
    #
    wceq
    #
    @11
    @57
    @66
    wb
    @65
    @56
    @20
    eqcom
    a1i
    @65
    @19
    cc
    wcel
    #
    @56
    cc
    wcel
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    #
    @66
    @68
    wb
    @63
    @69
    @64
    @2
    @69
    @1
    @2
    cP
    cc
    wcel
    #
    @69
    @2
    cP
    @45
    nncnd
    #
    cP
    peano2cnm
    syl
    adantl
    adantr
    @65
    @56
    @65
    @6
    @49
    @63
    @64
    simpr
    @1
    @59
    @2
    @64
    @62
    ad2antrr
    nnmulcld
    nncnd
    @70
    @65
    2cnne0
    a1i
    @19
    @56
    c2
    divmul3
    syl3anc
    @65
    @68
    @19
    @9
    wceq
    @10
    cP
    wceq
    #
    @11
    @65
    @67
    @9
    @19
    @65
    @67
    @6
    @49
    c2
    cmul
    co
    #
    cmul
    co
    @9
    @65
    @6
    @49
    c2
    @64
    @6
    cc
    wcel
    @63
    @6
    nncn
    adantl
    #
    @1
    @49
    cc
    wcel
    @2
    @64
    @1
    @49
    @62
    nncnd
    ad2antrr
    @65
    2cnd
    mulassd
    @65
    @74
    @8
    @6
    cmul
    @1
    @74
    @8
    wceq
    #
    @2
    @64
    @1
    @52
    @76
    @53
    @52
    c2
    @48
    c1
    caddc
    co
    #
    cexp
    co
    @74
    @8
    @52
    c2
    @48
    @52
    2cnd
    @52
    @48
    @61
    nnnn0d
    expp1d
    @52
    @77
    @7
    c2
    cexp
    @52
    cN
    cc
    wcel
    @77
    @7
    wceq
    cN
    nncn
    cN
    add1p1
    syl
    oveq2d
    eqtr3d
    syl
    ad2antrr
    oveq2d
    eqtrd
    eqeq2d
    @65
    cP
    c1
    @9
    @63
    @71
    @64
    @2
    @71
    @1
    @72
    adantl
    adantr
    @65
    1cnd
    @65
    @6
    @8
    @75
    @1
    @8
    cc
    wcel
    @2
    @64
    @1
    @8
    @1
    c2
    @7
    @60
    @1
    @52
    @7
    cn0
    wcel
    @53
    @52
    @7
    @52
    cN
    c2
    @52
    id
    @33
    @52
    2nn
    a1i
    nnaddcld
    nnnn0d
    syl
    nnexpcld
    nncnd
    ad2antrr
    mulcld
    subadd2d
    @73
    @11
    wb
    @65
    @10
    cP
    eqcom
    a1i
    3bitrd
    3bitrd
    rexbidva
    biimpd
    adantrr
    sylbid
    expr
    3adant3
    impcom
    adantr
    sylbid
    ex
    mpd
    sylbid
    sylbid
    mpd
    ex
    pm2.61i
end
