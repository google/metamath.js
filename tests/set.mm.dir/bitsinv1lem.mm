include "cbits.mm"
include "cfv.mm"
include "wcel.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmo.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "cz.mm"
include "cn0.mm"
include "wa.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "cmin.mm"
include "cc.mm"
include "simpl.mm"
include "cn.mm"
include "2nn.mm"
include "a1i.mm"
include "simpr.mm"
include "nnexpcld.mm"
include "zmodcld.mm"
include "nn0cnd.mm"
include "adantr.mm"
include "1nn0.mm"
include "nn0addcld.mm"
include "pncan3d.mm"
include "subcld.mm"
include "simplr.mm"
include "nncnd.mm"
include "wne.mm"
include "2cnd.mm"
include "2ne0.mm"
include "nn0zd.mm"
include "expne0d.mm"
include "cdiv.mm"
include "wn.mm"
include "cdvds.mm"
include "wbr.mm"
include "2z.mm"
include "dvds0.mm"
include "ax-mp.mm"
include "id.mm"
include "syl5breqr.mm"
include "cfl.mm"
include "bitsval2.mm"
include "cr.mm"
include "crp.mm"
include "zred.mm"
include "nnrpd.mm"
include "moddiffl.mm"
include "syl2anc.mm"
include "breq2d.mm"
include "wb.mm"
include "moddifz.mm"
include "zcnd.mm"
include "nnncan1d.mm"
include "oveq1d.mm"
include "divsubdird.mm"
include "eqtr3d.mm"
include "cmul.mm"
include "mulcomd.mm"
include "expp1d.mm"
include "eqtr4d.mm"
include "oveq12d.mm"
include "divcan5d.mm"
include "peano2zd.mm"
include "div23d.mm"
include "3eqtr3d.mm"
include "zmulcld.mm"
include "eqeltrd.mm"
include "zsubcld.mm"
include "dvdsmul2.mm"
include "nnncan2d.mm"
include "breqtrrd.mm"
include "dvdssub2.mm"
include "syl31anc.mm"
include "bitr3d.mm"
include "notbid.mm"
include "bitrd.mm"
include "con2bid.mm"
include "syl5ib.mm"
include "con2d.mm"
include "cpr.mm"
include "wo.mm"
include "cfzo.mm"
include "cuz.mm"
include "clt.mm"
include "cle.mm"
include "cneg.mm"
include "df-neg.mm"
include "mulm1d.mm"
include "nnred.mm"
include "renegcld.mm"
include "modcld.mm"
include "resubcld.mm"
include "modlt.mm"
include "ltnegd.mm"
include "mpbid.mm"
include "0red.mm"
include "modge0.mm"
include "lesub1dd.mm"
include "syl5eqbr.mm"
include "ltletrd.mm"
include "eqbrtrd.mm"
include "1red.mm"
include "ltmuldivd.mm"
include "syl5eqbrr.mm"
include "0zd.mm"
include "zlem1lt.mm"
include "mpbird.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "subge02d.mm"
include "lelttrd.mm"
include "breqtrd.mm"
include "ltdivmuld.mm"
include "elfzo2.mm"
include "syl3anbrc.mm"
include "fzo0to2pr.mm"
include "elpri.mm"
include "syl.mm"
include "ord.mm"
include "syld.mm"
include "imp.mm"
include "diveq1d.mm"
include "oveq2d.mm"
include "n2dvds1.mm"
include "breq2.mm"
include "mtbiri.mm"
include "syl6.mm"
include "sylibrd.mm"
include "con1d.mm"
include "diveq0d.mm"
include "subeq0d.mm"
include "addid1d.mm"
include "ifbothda.mm"

theorem bitsinv1lem
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let vy: setvar y


  assert |- ( ( N e. ZZ /\ M e. NN0 ) -> ( N mod ( 2 ^ ( M + 1 ) ) ) = ( ( N mod ( 2 ^ M ) ) + if ( M e. ( bits ` N ) , ( 2 ^ M ) , 0 ) ) )

  proof
    cM
    cN
    cbits
    cfv
    wcel
    #
    cN
    c2
    cM
    c1
    caddc
    co
    #
    cexp
    co
    #
    cmo
    co
    #
    cN
    c2
    cM
    cexp
    co
    #
    cmo
    co
    #
    @4
    caddc
    co
    #
    wceq
    @3
    @5
    cc0
    caddc
    co
    #
    wceq
    @3
    @5
    @0
    @4
    cc0
    cif
    #
    caddc
    co
    #
    wceq
    cN
    cz
    wcel
    #
    cM
    cn0
    wcel
    #
    wa
    #
    @4
    cc0
    @4
    @8
    wceq
    @6
    @9
    @3
    @4
    @8
    @5
    caddc
    oveq2
    eqeq2d
    cc0
    @8
    wceq
    @7
    @9
    @3
    cc0
    @8
    @5
    caddc
    oveq2
    eqeq2d
    @12
    @0
    wa
    #
    @5
    @3
    @5
    cmin
    co
    #
    caddc
    co
    @3
    @6
    @13
    @5
    @3
    @12
    @5
    cc
    wcel
    #
    @0
    @12
    @5
    @12
    cN
    @4
    @10
    @11
    simpl
    #
    @12
    c2
    cM
    c2
    cn
    wcel
    #
    @12
    2nn
    a1i
    #
    @10
    @11
    simpr
    #
    nnexpcld
    #
    zmodcld
    nn0cnd
    #
    adantr
    @12
    @3
    cc
    wcel
    #
    @0
    @12
    @3
    @12
    cN
    @2
    @16
    @12
    c2
    @1
    @18
    @12
    cM
    c1
    @19
    c1
    cn0
    wcel
    @12
    1nn0
    a1i
    nn0addcld
    nnexpcld
    #
    zmodcld
    nn0cnd
    #
    adantr
    pncan3d
    @13
    @14
    @4
    @5
    caddc
    @13
    @14
    @4
    @12
    @14
    cc
    wcel
    #
    @0
    @12
    @3
    @5
    @24
    @21
    subcld
    #
    adantr
    @13
    @4
    @13
    c2
    cM
    @17
    @13
    2nn
    a1i
    @10
    @11
    @0
    simplr
    nnexpcld
    nncnd
    @12
    @4
    cc0
    wne
    #
    @0
    @12
    c2
    cM
    @12
    2cnd
    #
    c2
    cc0
    wne
    @12
    2ne0
    a1i
    #
    @12
    cM
    @19
    nn0zd
    #
    expne0d
    #
    adantr
    @12
    @0
    @14
    @4
    cdiv
    co
    #
    c1
    wceq
    #
    @12
    @0
    @32
    cc0
    wceq
    #
    wn
    #
    @33
    @12
    @34
    @0
    @34
    c2
    @32
    cdvds
    wbr
    #
    @12
    @0
    wn
    #
    @34
    c2
    cc0
    @32
    cdvds
    c2
    cz
    wcel
    #
    c2
    cc0
    cdvds
    wbr
    2z
    c2
    dvds0
    ax-mp
    @34
    id
    syl5breqr
    @12
    @0
    @36
    @12
    @0
    c2
    cN
    @4
    cdiv
    co
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    @36
    wn
    #
    cM
    cN
    bitsval2
    @12
    @40
    @36
    @12
    c2
    cN
    @5
    cmin
    co
    #
    @4
    cdiv
    co
    #
    cdvds
    wbr
    #
    @40
    @36
    @12
    @43
    @39
    c2
    cdvds
    @12
    cN
    cr
    wcel
    #
    @4
    crp
    wcel
    #
    @43
    @39
    wceq
    @12
    cN
    @16
    zred
    #
    @12
    @4
    @20
    nnrpd
    #
    cN
    @4
    moddiffl
    syl2anc
    breq2d
    @12
    @38
    @43
    cz
    wcel
    #
    @32
    cz
    wcel
    #
    c2
    @43
    @32
    cmin
    co
    #
    cdvds
    wbr
    @44
    @36
    wb
    @38
    @12
    2z
    a1i
    #
    @12
    @45
    @46
    @49
    @47
    @48
    cN
    @4
    moddifz
    syl2anc
    #
    @12
    @32
    @43
    cN
    @3
    cmin
    co
    #
    @4
    cdiv
    co
    #
    cmin
    co
    #
    cz
    @12
    @42
    @54
    cmin
    co
    #
    @4
    cdiv
    co
    @32
    @56
    @12
    @57
    @14
    @4
    cdiv
    @12
    cN
    @5
    @3
    @12
    cN
    @16
    zcnd
    #
    @21
    @24
    nnncan1d
    oveq1d
    @12
    @42
    @54
    @4
    @12
    cN
    @5
    @58
    @21
    subcld
    #
    @12
    cN
    @3
    @58
    @24
    subcld
    #
    @12
    @4
    @20
    nncnd
    #
    @31
    divsubdird
    eqtr3d
    @12
    @43
    @55
    @53
    @12
    @55
    @54
    @2
    cdiv
    co
    #
    c2
    cmul
    co
    #
    cz
    @12
    c2
    @54
    cmul
    co
    #
    c2
    @4
    cmul
    co
    #
    cdiv
    co
    @54
    c2
    cmul
    co
    #
    @2
    cdiv
    co
    @55
    @63
    @12
    @64
    @66
    @65
    @2
    cdiv
    @12
    c2
    @54
    @28
    @60
    mulcomd
    @12
    @65
    @4
    c2
    cmul
    co
    #
    @2
    @12
    c2
    @4
    @28
    @61
    mulcomd
    @12
    c2
    cM
    @28
    @19
    expp1d
    #
    eqtr4d
    oveq12d
    @12
    @54
    @4
    c2
    @60
    @61
    @28
    @31
    @29
    divcan5d
    @12
    @54
    c2
    @2
    @60
    @28
    @12
    @2
    @23
    nncnd
    @12
    c2
    @1
    @28
    @29
    @12
    cM
    @30
    peano2zd
    expne0d
    div23d
    3eqtr3d
    #
    @12
    @62
    c2
    @12
    @45
    @2
    crp
    wcel
    #
    @62
    cz
    wcel
    #
    @47
    @12
    @2
    @23
    nnrpd
    #
    cN
    @2
    moddifz
    syl2anc
    #
    @52
    zmulcld
    eqeltrd
    zsubcld
    eqeltrd
    #
    @12
    c2
    @63
    @51
    cdvds
    @12
    @71
    @38
    c2
    @63
    cdvds
    wbr
    @73
    @52
    @62
    c2
    dvdsmul2
    syl2anc
    @12
    @42
    @14
    cmin
    co
    #
    @4
    cdiv
    co
    @55
    @51
    @63
    @12
    @75
    @54
    @4
    cdiv
    @12
    cN
    @3
    @5
    @58
    @24
    @21
    nnncan2d
    oveq1d
    @12
    @42
    @14
    @4
    @59
    @26
    @61
    @31
    divsubdird
    @69
    3eqtr3d
    breqtrrd
    c2
    @43
    @32
    dvdssub2
    syl31anc
    bitr3d
    notbid
    bitrd
    #
    con2bid
    syl5ib
    con2d
    @12
    @34
    @33
    @12
    @32
    cc0
    c1
    cpr
    #
    wcel
    @34
    @33
    wo
    @12
    @32
    cc0
    c2
    cfzo
    co
    #
    @77
    @12
    @32
    cc0
    cuz
    cfv
    #
    wcel
    @38
    @32
    c2
    clt
    wbr
    #
    @32
    @78
    wcel
    @12
    @32
    cn0
    @79
    @12
    @50
    cc0
    @32
    cle
    wbr
    #
    @32
    cn0
    wcel
    @74
    @12
    @81
    cc0
    c1
    cmin
    co
    #
    @32
    clt
    wbr
    #
    @12
    @82
    c1
    cneg
    #
    @32
    clt
    c1
    df-neg
    @12
    @84
    @4
    cmul
    co
    #
    @14
    clt
    wbr
    @84
    @32
    clt
    wbr
    @12
    @85
    @4
    cneg
    #
    @14
    clt
    @12
    @4
    @61
    mulm1d
    @12
    @86
    @5
    cneg
    #
    @14
    @12
    @4
    @12
    @4
    @20
    nnred
    #
    renegcld
    @12
    @5
    @12
    cN
    @4
    @47
    @48
    modcld
    #
    renegcld
    @12
    @3
    @5
    @12
    cN
    @2
    @47
    @72
    modcld
    #
    @89
    resubcld
    #
    @12
    @5
    @4
    clt
    wbr
    #
    @86
    @87
    clt
    wbr
    @12
    @45
    @46
    @92
    @47
    @48
    cN
    @4
    modlt
    syl2anc
    @12
    @5
    @4
    @89
    @88
    ltnegd
    mpbid
    @12
    @87
    cc0
    @5
    cmin
    co
    @14
    cle
    @5
    df-neg
    @12
    cc0
    @3
    @5
    @12
    0red
    @90
    @89
    @12
    @45
    @70
    cc0
    @3
    cle
    wbr
    @47
    @72
    cN
    @2
    modge0
    syl2anc
    lesub1dd
    syl5eqbr
    ltletrd
    eqbrtrd
    @12
    @84
    @14
    @4
    @12
    c1
    @12
    1red
    renegcld
    @91
    @48
    ltmuldivd
    mpbid
    syl5eqbrr
    @12
    cc0
    cz
    wcel
    @50
    @81
    @83
    wb
    @12
    0zd
    @74
    cc0
    @32
    zlem1lt
    syl2anc
    mpbird
    @32
    elnn0z
    sylanbrc
    nn0uz
    syl6eleq
    @52
    @12
    @80
    @14
    @67
    clt
    wbr
    @12
    @14
    @2
    @67
    clt
    @12
    @14
    @3
    @2
    @91
    @90
    @12
    @2
    @23
    nnred
    @12
    cc0
    @5
    cle
    wbr
    #
    @14
    @3
    cle
    wbr
    @12
    @45
    @46
    @93
    @47
    @48
    cN
    @4
    modge0
    syl2anc
    @12
    @3
    @5
    @90
    @89
    subge02d
    mpbid
    @12
    @45
    @70
    @3
    @2
    clt
    wbr
    @47
    @72
    cN
    @2
    modlt
    syl2anc
    lelttrd
    @68
    breqtrd
    @12
    @14
    c2
    @4
    @91
    @12
    c2
    @18
    nnred
    @48
    ltdivmuld
    mpbird
    @32
    cc0
    c2
    elfzo2
    syl3anbrc
    fzo0to2pr
    syl6eleq
    @32
    cc0
    c1
    elpri
    syl
    ord
    #
    syld
    imp
    diveq1d
    oveq2d
    eqtr3d
    @12
    @37
    wa
    #
    @3
    @5
    @7
    @95
    @3
    @5
    @12
    @22
    @37
    @24
    adantr
    @12
    @15
    @37
    @21
    adantr
    #
    @95
    @14
    @4
    @12
    @25
    @37
    @26
    adantr
    @12
    @4
    cc
    wcel
    @37
    @61
    adantr
    @12
    @27
    @37
    @31
    adantr
    @12
    @37
    @34
    @12
    @34
    @0
    @12
    @35
    @41
    @0
    @12
    @35
    @33
    @41
    @94
    @33
    @36
    c2
    c1
    cdvds
    wbr
    n2dvds1
    @32
    c1
    c2
    cdvds
    breq2
    mtbiri
    syl6
    @76
    sylibrd
    con1d
    imp
    diveq0d
    subeq0d
    @95
    @5
    @96
    addid1d
    eqtr4d
    ifbothda
end
