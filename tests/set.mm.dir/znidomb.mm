include "cn.mm"
include "wcel.mm"
include "cidom.mm"
include "cprime.mm"
include "wa.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "c1.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "cz.mm"
include "cle.mm"
include "2z.mm"
include "a1i.mm"
include "nnz.mm"
include "adantr.mm"
include "cbs.mm"
include "chash.mm"
include "c2o.mm"
include "hash2.mm"
include "cdom.mm"
include "cnzr.mm"
include "cdomn.mm"
include "ccrg.mm"
include "isidom.mm"
include "simprbi.mm"
include "domnnzr.mm"
include "syl.mm"
include "crg.mm"
include "eqid.mm"
include "isnzr2.mm"
include "adantl.mm"
include "cfn.mm"
include "cvv.mm"
include "wb.mm"
include "c0.mm"
include "csn.mm"
include "cpr.mm"
include "df2o2.mm"
include "prfi.mm"
include "eqeltri.mm"
include "fvex.mm"
include "hashdom.mm"
include "mp2an.mm"
include "sylibr.mm"
include "syl5eqbrr.mm"
include "znhash.mm"
include "breqtrd.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "cdiv.mm"
include "co.mm"
include "czrh.mm"
include "c0g.mm"
include "cmulr.mm"
include "cmul.mm"
include "cc.mm"
include "nncn.mm"
include "ad2antrr.mm"
include "ad2antrl.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divcan1d.mm"
include "fveq2d.mm"
include "zring.mm"
include "crh.mm"
include "ad2antlr.mm"
include "domnring.mm"
include "zrhrhm.mm"
include "simprr.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "zringbas.mm"
include "zringmulr.mm"
include "rhmmul.mm"
include "iddvds.mm"
include "cn0.mm"
include "nnnn0.mm"
include "zndvds0.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "3eqtr3d.mm"
include "wf.mm"
include "rhmf.mm"
include "ffvelrnd.mm"
include "domneq0.mm"
include "clt.mm"
include "cr.mm"
include "nnre.mm"
include "nngt0.mm"
include "divgt0d.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "dvdsle.mm"
include "1red.mm"
include "0lt1.mm"
include "lediv2.mm"
include "syl222anc.mm"
include "nnle1eq1.mm"
include "div1d.mm"
include "breq1d.mm"
include "3bitr3rd.mm"
include "sylibd.mm"
include "sylbid.mm"
include "dvdseq.mm"
include "expr.mm"
include "syl21anc.mm"
include "orim12d.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "isprm2.mm"
include "ex.mm"
include "cfield.mm"
include "znfld.mm"
include "fldidom.mm"
include "impbid1.mm"

theorem znidomb
  let cN: class N
  let cY: class Y
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume zntos.y: |- Y = ( Z/nZ ` N )


  assert |- ( N e. NN -> ( Y e. IDomn <-> N e. Prime ) )

  proof
    cN
    cn
    wcel
    #
    cY
    cidom
    wcel
    #
    cN
    cprime
    wcel
    #
    @0
    @1
    @2
    @0
    @1
    wa
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    vx
    cv
    #
    cN
    cdvds
    wbr
    #
    @5
    c1
    wceq
    #
    @5
    cN
    wceq
    #
    wo
    #
    wi
    #
    vx
    cn
    wral
    @2
    @3
    c2
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    c2
    cN
    cle
    wbr
    @4
    @11
    @3
    2z
    a1i
    @0
    @12
    @1
    cN
    nnz
    #
    adantr
    @3
    c2
    cY
    cbs
    cfv
    #
    chash
    cfv
    #
    cN
    cle
    @3
    c2
    c2o
    chash
    cfv
    #
    @15
    cle
    hash2
    @3
    c2o
    @14
    cdom
    wbr
    #
    @16
    @15
    cle
    wbr
    #
    @1
    @17
    @0
    @1
    cY
    cnzr
    wcel
    #
    @17
    @1
    cY
    cdomn
    wcel
    #
    @19
    @1
    cY
    ccrg
    wcel
    @20
    cY
    isidom
    simprbi
    #
    cY
    domnnzr
    syl
    @19
    cY
    crg
    wcel
    #
    @17
    @14
    cY
    @14
    eqid
    #
    isnzr2
    simprbi
    syl
    adantl
    c2o
    cfn
    wcel
    @14
    cvv
    wcel
    @18
    @17
    wb
    c2o
    c0
    c0
    csn
    #
    cpr
    cfn
    df2o2
    c0
    @24
    prfi
    eqeltri
    cY
    cbs
    fvex
    c2o
    @14
    cvv
    hashdom
    mp2an
    sylibr
    syl5eqbrr
    @0
    @15
    cN
    wceq
    @1
    @14
    cN
    cY
    zntos.y
    @23
    znhash
    adantr
    breqtrd
    c2
    cN
    eluz2
    syl3anbrc
    @3
    @10
    vx
    cn
    @3
    @5
    cn
    wcel
    #
    @6
    @9
    @3
    @25
    @6
    wa
    #
    wa
    #
    cN
    @5
    cdiv
    co
    #
    cY
    czrh
    cfv
    #
    cfv
    #
    cY
    c0g
    cfv
    #
    wceq
    #
    @5
    @29
    cfv
    #
    @31
    wceq
    #
    wo
    #
    @9
    @27
    @30
    @33
    cY
    cmulr
    cfv
    #
    co
    #
    @31
    wceq
    #
    @35
    @27
    @28
    @5
    cmul
    co
    #
    @29
    cfv
    #
    cN
    @29
    cfv
    #
    @37
    @31
    @27
    @39
    cN
    @29
    @27
    cN
    @5
    @0
    cN
    cc
    wcel
    @1
    @26
    cN
    nncn
    ad2antrr
    #
    @25
    @5
    cc
    wcel
    @3
    @6
    @5
    nncn
    ad2antrl
    @25
    @5
    cc0
    wne
    #
    @3
    @6
    @5
    nnne0
    ad2antrl
    #
    divcan1d
    fveq2d
    @27
    @29
    zring
    cY
    crh
    co
    wcel
    #
    @28
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    @40
    @37
    wceq
    @27
    @22
    @45
    @27
    @20
    @22
    @1
    @20
    @0
    @26
    @21
    ad2antlr
    #
    cY
    domnring
    syl
    cY
    @29
    @29
    eqid
    #
    zrhrhm
    syl
    #
    @27
    @6
    @46
    @3
    @25
    @6
    simprr
    #
    @27
    @47
    @43
    @12
    @6
    @46
    wb
    @25
    @47
    @3
    @6
    @5
    nnz
    ad2antrl
    #
    @44
    @0
    @12
    @1
    @26
    @13
    ad2antrr
    #
    @5
    cN
    dvdsval2
    syl3anc
    mpbid
    #
    @52
    @28
    @5
    zring
    cY
    cmul
    @36
    @29
    cz
    zringbas
    zringmulr
    @36
    eqid
    #
    rhmmul
    syl3anc
    @27
    @41
    @31
    wceq
    #
    cN
    cN
    cdvds
    wbr
    #
    @27
    @12
    @57
    @53
    cN
    iddvds
    syl
    @27
    cN
    cn0
    wcel
    #
    @12
    @56
    @57
    wb
    @0
    @58
    @1
    @26
    cN
    nnnn0
    ad2antrr
    #
    @53
    cN
    @29
    cN
    cY
    @31
    zntos.y
    @49
    @31
    eqid
    #
    zndvds0
    syl2anc
    mpbird
    3eqtr3d
    @27
    @20
    @30
    @14
    wcel
    @33
    @14
    wcel
    @38
    @35
    wb
    @48
    @27
    cz
    @14
    @28
    @29
    @27
    @45
    cz
    @14
    @29
    wf
    @50
    cz
    @14
    zring
    cY
    @29
    zringbas
    @23
    rhmf
    syl
    #
    @54
    ffvelrnd
    @27
    cz
    @14
    @5
    @29
    @61
    @52
    ffvelrnd
    @14
    cY
    @36
    @30
    @33
    @31
    @23
    @55
    @60
    domneq0
    syl3anc
    mpbid
    @27
    @32
    @7
    @34
    @8
    @27
    @32
    cN
    @28
    cdvds
    wbr
    #
    @7
    @27
    @58
    @46
    @32
    @62
    wb
    @59
    @54
    @28
    @29
    cN
    cY
    @31
    zntos.y
    @49
    @60
    zndvds0
    syl2anc
    @27
    @62
    cN
    @28
    cle
    wbr
    #
    @7
    @27
    @12
    @28
    cn
    wcel
    #
    @62
    @63
    wi
    @53
    @27
    @46
    cc0
    @28
    clt
    wbr
    @64
    @54
    @27
    cN
    @5
    @0
    cN
    cr
    wcel
    #
    @1
    @26
    cN
    nnre
    ad2antrr
    #
    @25
    @5
    cr
    wcel
    #
    @3
    @6
    @5
    nnre
    ad2antrl
    #
    @0
    cc0
    cN
    clt
    wbr
    #
    @1
    @26
    cN
    nngt0
    ad2antrr
    #
    @25
    cc0
    @5
    clt
    wbr
    #
    @3
    @6
    @5
    nngt0
    ad2antrl
    #
    divgt0d
    @28
    elnnz
    sylanbrc
    cN
    @28
    dvdsle
    syl2anc
    @27
    @5
    c1
    cle
    wbr
    #
    cN
    c1
    cdiv
    co
    #
    @28
    cle
    wbr
    #
    @7
    @63
    @27
    @67
    @71
    c1
    cr
    wcel
    cc0
    c1
    clt
    wbr
    #
    @65
    @69
    @73
    @75
    wb
    @68
    @72
    @27
    1red
    @76
    @27
    0lt1
    a1i
    @66
    @70
    @5
    c1
    cN
    lediv2
    syl222anc
    @25
    @73
    @7
    wb
    @3
    @6
    @5
    nnle1eq1
    ad2antrl
    @27
    @74
    cN
    @28
    cle
    @27
    cN
    @42
    div1d
    breq1d
    3bitr3rd
    sylibd
    sylbid
    @27
    @34
    cN
    @5
    cdvds
    wbr
    #
    @8
    @27
    @58
    @47
    @34
    @77
    wb
    @59
    @52
    @5
    @29
    cN
    cY
    @31
    zntos.y
    @49
    @60
    zndvds0
    syl2anc
    @27
    @5
    cn0
    wcel
    #
    @58
    @6
    @77
    @8
    wi
    @25
    @78
    @3
    @6
    @5
    nnnn0
    ad2antrl
    @59
    @51
    @78
    @58
    wa
    @6
    @77
    @8
    @5
    cN
    dvdseq
    expr
    syl21anc
    sylbid
    orim12d
    mpd
    expr
    ralrimiva
    vx
    cN
    isprm2
    sylanbrc
    ex
    @2
    cY
    cfield
    wcel
    @1
    cN
    cY
    zntos.y
    znfld
    cY
    fldidom
    syl
    impbid1
end
