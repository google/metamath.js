include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cbc.mm"
include "cmul.mm"
include "cid.mm"
include "cmin.mm"
include "c1.mm"
include "caddc.mm"
include "cseq.mm"
include "cfv.mm"
include "cfa.mm"
include "cdiv.mm"
include "wceq.mm"
include "bcval2.mm"
include "adantl.mm"
include "cc.mm"
include "cv.mm"
include "mulcl.mm"
include "w3a.mm"
include "mulass.mm"
include "cuz.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "simplr.mm"
include "elfzuz3.mm"
include "eluznn.mm"
include "syl2anc.mm"
include "adantrr.mm"
include "cr.mm"
include "crp.mm"
include "nnre.mm"
include "nnrp.mm"
include "ltsubrp.mm"
include "syl2an.mm"
include "cz.mm"
include "wb.mm"
include "nnzd.mm"
include "nnz.mm"
include "ad2antlr.mm"
include "zsubcld.mm"
include "zltp1le.mm"
include "mpbid.mm"
include "peano2zd.mm"
include "eluz.mm"
include "mpbird.mm"
include "simprr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "fvi.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "eqeltrd.mm"
include "seqsplit.mm"
include "facnn.mm"
include "syl.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "expr.mm"
include "simpll.mm"
include "faccl.mm"
include "nncn.mm"
include "3syl.mm"
include "mulid2d.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "fveq2.mm"
include "fac0.mm"
include "syl6eq.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "seqeq1d.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "wo.mm"
include "fznn0sub.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaod.mm"
include "eqid.mm"
include "nn0z.mm"
include "zsubcl.mm"
include "adantr.mm"
include "eluzelcn.mm"
include "seqf.mm"
include "ffvelrnd.mm"
include "elfznn0.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan5d.mm"
include "3eqtrd.mm"
include "wn.mm"
include "nnnn0.mm"
include "nnne0.mm"
include "div0d.mm"
include "mul02.mm"
include "mul01.mm"
include "simpr.mm"
include "nn0uz.mm"
include "ad2antrr.mm"
include "elfz5.mm"
include "nn0re.mm"
include "subge0d.mm"
include "bitr4d.mm"
include "mtbid.mm"
include "zred.mm"
include "0re.mm"
include "ltnle.mm"
include "sylancl.mm"
include "0z.mm"
include "nn0ge0.mm"
include "0zd.mm"
include "elfz.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "0cn.mm"
include "mp1i.mm"
include "seqz.mm"
include "bcval3.mm"
include "syl3an2.mm"
include "3expa.mm"
include "3eqtr4rd.mm"
include "pm2.61dan.mm"

theorem bcval5
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( N e. NN0 /\ K e. NN ) -> ( N _C K ) = ( ( seq ( ( N - K ) + 1 ) ( x. , _I ) ` N ) / ( ! ` K ) ) )

  proof
    cN
    cn0
    wcel
    #
    cK
    cn
    wcel
    #
    wa
    #
    cK
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cK
    cbc
    co
    #
    cN
    cmul
    cid
    cN
    cK
    cmin
    co
    #
    c1
    caddc
    co
    #
    cseq
    #
    cfv
    #
    cK
    cfa
    cfv
    #
    cdiv
    co
    #
    wceq
    @2
    @3
    wa
    #
    @4
    cN
    cfa
    cfv
    #
    @5
    cfa
    cfv
    #
    @9
    cmul
    co
    #
    cdiv
    co
    #
    @13
    @8
    cmul
    co
    #
    @14
    cdiv
    co
    @10
    @3
    @4
    @15
    wceq
    @2
    cK
    cN
    bcval2
    adantl
    @11
    @12
    @16
    @14
    cdiv
    @11
    @5
    cn
    wcel
    #
    @12
    @16
    wceq
    #
    @5
    cc0
    wceq
    #
    @2
    @3
    @17
    @18
    @2
    @3
    @17
    wa
    #
    wa
    #
    cN
    cmul
    cid
    c1
    cseq
    #
    cfv
    #
    @5
    @22
    cfv
    #
    @8
    cmul
    co
    @12
    @16
    @21
    vk
    vx
    vy
    cmul
    cc
    cid
    c1
    @5
    cN
    vk
    cv
    #
    cc
    wcel
    #
    vx
    cv
    #
    cc
    wcel
    #
    wa
    #
    @25
    @27
    cmul
    co
    #
    cc
    wcel
    #
    @21
    @25
    @27
    mulcl
    #
    adantl
    @26
    @28
    vy
    cv
    #
    cc
    wcel
    w3a
    @30
    @33
    cmul
    co
    @25
    @27
    @33
    cmul
    co
    cmul
    co
    wceq
    @21
    @25
    @27
    @33
    mulass
    adantl
    @21
    cN
    @6
    cuz
    cfv
    #
    wcel
    #
    @6
    cN
    cle
    wbr
    #
    @21
    @5
    cN
    clt
    wbr
    #
    @36
    @21
    cN
    cn
    wcel
    #
    @1
    @37
    @2
    @3
    @38
    @17
    @11
    @1
    cN
    cK
    cuz
    cfv
    wcel
    #
    @38
    @0
    @1
    @3
    simplr
    #
    @3
    @39
    @2
    cK
    cc0
    cN
    elfzuz3
    adantl
    cN
    cK
    eluznn
    syl2anc
    #
    adantrr
    #
    @0
    @1
    @20
    simplr
    @38
    cN
    cr
    wcel
    #
    cK
    crp
    wcel
    @37
    @1
    cN
    nnre
    cK
    nnrp
    cN
    cK
    ltsubrp
    syl2an
    #
    syl2anc
    @21
    @5
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @37
    @36
    wb
    #
    @21
    cN
    cK
    @21
    cN
    @42
    nnzd
    #
    @1
    cK
    cz
    wcel
    #
    @0
    @20
    cK
    nnz
    #
    ad2antlr
    zsubcld
    #
    @48
    @5
    cN
    zltp1le
    #
    syl2anc
    mpbid
    @21
    @6
    cz
    wcel
    #
    @46
    @35
    @36
    wb
    #
    @21
    @5
    @51
    peano2zd
    @48
    @6
    cN
    eluz
    #
    syl2anc
    mpbird
    @21
    @5
    cn
    c1
    cuz
    cfv
    @2
    @3
    @17
    simprr
    #
    nnuz
    syl6eleq
    @25
    c1
    cN
    cfz
    co
    #
    wcel
    #
    @25
    cid
    cfv
    #
    cc
    wcel
    #
    @21
    @58
    @59
    @25
    cc
    @25
    @57
    fvi
    @58
    @25
    @25
    c1
    cN
    elfzelz
    zcnd
    eqeltrd
    adantl
    seqsplit
    @21
    @38
    @12
    @23
    wceq
    #
    @42
    cN
    facnn
    #
    syl
    @21
    @13
    @24
    @8
    cmul
    @21
    @17
    @13
    @24
    wceq
    @56
    @5
    facnn
    syl
    oveq1d
    3eqtr4d
    expr
    @11
    @18
    @19
    @12
    c1
    @23
    cmul
    co
    #
    wceq
    @11
    c1
    @12
    cmul
    co
    @12
    @63
    @11
    @12
    @11
    @0
    @12
    cn
    wcel
    @12
    cc
    wcel
    @0
    @1
    @3
    simpll
    cN
    faccl
    @12
    nncn
    3syl
    mulid2d
    @11
    @12
    @23
    c1
    cmul
    @11
    @38
    @61
    @41
    @62
    syl
    oveq2d
    eqtr3d
    @19
    @16
    @63
    @12
    @19
    @13
    c1
    @8
    @23
    cmul
    @19
    @13
    cc0
    cfa
    cfv
    c1
    @5
    cc0
    cfa
    fveq2
    fac0
    syl6eq
    @19
    cN
    @7
    @22
    @19
    @6
    c1
    cmul
    cid
    @19
    @6
    cc0
    c1
    caddc
    co
    c1
    @5
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    seqeq1d
    fveq1d
    oveq12d
    eqeq2d
    syl5ibrcom
    @11
    @5
    cn0
    wcel
    #
    @17
    @19
    wo
    @3
    @64
    @2
    cK
    cc0
    cN
    fznn0sub
    adantl
    #
    @5
    elnn0
    sylib
    mpjaod
    oveq1d
    @11
    @8
    @9
    @13
    @11
    @34
    cc
    cN
    @7
    @11
    vk
    vx
    cmul
    cc
    cid
    @6
    @34
    @34
    eqid
    @2
    @53
    @3
    @2
    @5
    @0
    @46
    @49
    @45
    @1
    cN
    nn0z
    #
    @50
    cN
    cK
    zsubcl
    syl2an
    #
    peano2zd
    #
    adantr
    #
    @25
    @34
    wcel
    #
    @60
    @11
    @70
    @59
    @25
    cc
    @25
    @34
    fvi
    @6
    @25
    eluzelcn
    eqeltrd
    adantl
    @29
    @31
    @11
    @32
    adantl
    seqf
    @11
    @35
    @36
    @11
    @37
    @36
    @11
    @38
    @1
    @37
    @41
    @40
    @44
    syl2anc
    @11
    @45
    @46
    @47
    @2
    @45
    @3
    @67
    adantr
    @11
    cN
    @41
    nnzd
    #
    @52
    syl2anc
    mpbid
    @11
    @53
    @46
    @54
    @69
    @71
    @55
    syl2anc
    mpbird
    ffvelrnd
    @11
    @9
    @11
    cK
    cn0
    wcel
    #
    @9
    cn
    wcel
    #
    @3
    @72
    @2
    cK
    cN
    elfznn0
    adantl
    cK
    faccl
    #
    syl
    #
    nncnd
    @11
    @13
    @11
    @64
    @13
    cn
    wcel
    @65
    @5
    faccl
    syl
    #
    nncnd
    @11
    @9
    @75
    nnne0d
    @11
    @13
    @76
    nnne0d
    divcan5d
    3eqtrd
    @2
    @3
    wn
    #
    wa
    #
    cc0
    @9
    cdiv
    co
    #
    cc0
    @10
    @4
    @78
    @72
    @73
    @79
    cc0
    wceq
    @1
    @72
    @0
    @77
    cK
    nnnn0
    ad2antlr
    #
    @74
    @73
    @9
    @9
    nncn
    @9
    nnne0
    div0d
    3syl
    @78
    @8
    cc0
    @9
    cdiv
    @78
    vk
    vx
    cmul
    cc
    cid
    cc0
    @6
    cN
    cn0
    cc0
    @29
    @31
    @78
    @32
    adantl
    @25
    @6
    cN
    cfz
    co
    #
    wcel
    #
    @60
    @78
    @82
    @59
    @25
    cc
    @25
    @81
    fvi
    @82
    @25
    @25
    @6
    cN
    elfzelz
    zcnd
    eqeltrd
    adantl
    @26
    cc0
    @25
    cmul
    co
    cc0
    wceq
    @78
    @25
    mul02
    adantl
    @26
    @25
    cc0
    cmul
    co
    cc0
    wceq
    @78
    @25
    mul01
    adantl
    @78
    cc0
    @81
    wcel
    #
    @6
    cc0
    cle
    wbr
    #
    cc0
    cN
    cle
    wbr
    #
    @78
    @5
    cc0
    clt
    wbr
    #
    @84
    @78
    @86
    cc0
    @5
    cle
    wbr
    #
    wn
    #
    @78
    @3
    @87
    @2
    @77
    simpr
    @78
    @3
    cK
    cN
    cle
    wbr
    #
    @87
    @78
    cK
    cc0
    cuz
    cfv
    #
    wcel
    @46
    @3
    @89
    wb
    @78
    cK
    cn0
    @90
    @80
    nn0uz
    syl6eleq
    @0
    @46
    @1
    @77
    @66
    ad2antrr
    #
    cK
    cc0
    cN
    elfz5
    syl2anc
    @78
    cN
    cK
    @0
    @43
    @1
    @77
    cN
    nn0re
    ad2antrr
    @1
    cK
    cr
    wcel
    @0
    @77
    cK
    nnre
    ad2antlr
    subge0d
    bitr4d
    mtbid
    @78
    @5
    cr
    wcel
    cc0
    cr
    wcel
    @86
    @88
    wb
    @78
    @5
    @2
    @45
    @77
    @67
    adantr
    #
    zred
    0re
    @5
    cc0
    ltnle
    sylancl
    mpbird
    @78
    @45
    cc0
    cz
    wcel
    #
    @86
    @84
    wb
    @92
    0z
    @5
    cc0
    zltp1le
    sylancl
    mpbid
    @0
    @85
    @1
    @77
    cN
    nn0ge0
    ad2antrr
    @78
    @93
    @53
    @46
    @83
    @84
    @85
    wa
    wb
    @78
    0zd
    @2
    @53
    @77
    @68
    adantr
    @91
    cc0
    @6
    cN
    elfz
    syl3anc
    mpbir2and
    @0
    @1
    @77
    simpll
    cc0
    cc
    wcel
    cc0
    cid
    cfv
    cc0
    wceq
    @78
    0cn
    cc0
    cc
    fvi
    mp1i
    seqz
    oveq1d
    @0
    @1
    @77
    @4
    cc0
    wceq
    #
    @1
    @0
    @49
    @77
    @94
    @50
    cK
    cN
    bcval3
    syl3an2
    3expa
    3eqtr4rd
    pm2.61dan
end
