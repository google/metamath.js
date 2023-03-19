include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wn.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "clog.mm"
include "cim.mm"
include "cneg.mm"
include "cdiv.mm"
include "cc0.mm"
include "wa.mm"
include "caddc.mm"
include "crp.mm"
include "1cnd.mm"
include "simpl1.mm"
include "negsubd.mm"
include "1rp.mm"
include "a1i.mm"
include "simpl3.mm"
include "wo.mm"
include "simpl2.mm"
include "cr.mm"
include "sub32d.mm"
include "1m1e0.mm"
include "oveq1i.mm"
include "df-neg.mm"
include "eqtr4i.mm"
include "syl6eq.mm"
include "simp1.mm"
include "subcld.mm"
include "adantr.mm"
include "wne.mm"
include "wb.mm"
include "ax-1cn.mm"
include "subeq0.mm"
include "mpan.mm"
include "biimpd.mm"
include "con3dimp.mm"
include "neqned.mm"
include "3adant2.mm"
include "recrecd.mm"
include "div2negd.mm"
include "ccj.mm"
include "negcld.mm"
include "cjdivd.mm"
include "cjnegd.mm"
include "fveq2.mm"
include "abs0.mm"
include "eqtr2.mm"
include "sylan2.mm"
include "ax-1ne0.mm"
include "id.mm"
include "neneqd.mm"
include "mp1i.mm"
include "pm2.65da.mm"
include "adantl.mm"
include "df-ne.mm"
include "cmul.mm"
include "c2.mm"
include "cexp.mm"
include "oveq1.mm"
include "sq1.mm"
include "absvalsq.mm"
include "eqtr3d.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "cjcld.mm"
include "simp3.mm"
include "divcan3d.mm"
include "eqtrd.mm"
include "syl3an3br.mm"
include "mpd3an3.mm"
include "eqcomd.mm"
include "negeqd.mm"
include "cjsub.mm"
include "1red.mm"
include "cjred.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "3ad2ant2.mm"
include "simpl.mm"
include "simpr.mm"
include "divnegd.mm"
include "syl2anc.mm"
include "divcld.mm"
include "reccld.mm"
include "cjne0d.mm"
include "eqnetrrd.mm"
include "divcan5d.mm"
include "divcan2d.mm"
include "subdid.mm"
include "mulid1d.mm"
include "recidd.mm"
include "oveq12d.mm"
include "3eqtr2d.mm"
include "subcl.mm"
include "negnegd.mm"
include "negsubdi2.mm"
include "reim0bd.mm"
include "eqeltrd.mm"
include "eqeltrrd.mm"
include "recne0d.mm"
include "rereccld.mm"
include "resubcld.mm"
include "negrebd.mm"
include "absord.mm"
include "eqeq1.mm"
include "orim12d.mm"
include "sylc.mm"
include "ord.mm"
include "mpd.mm"
include "rpaddcld.mm"
include "relogcld.mm"
include "reim0d.mm"
include "rpdivcld.mm"
include "eqtr4d.mm"
include "logcld.mm"
include "imcld.mm"
include "recnd.mm"
include "negne0d.mm"
include "divne0d.mm"
include "fveq2d.mm"
include "logcj.mm"
include "sylan.mm"
include "cpi.mm"
include "isosctrlem1.mm"
include "logrec.mm"
include "syl3anc.mm"
include "3eqtr4rd.mm"
include "3eqtr3rd.mm"
include "imnegd.mm"
include "imcjd.mm"
include "3eqtr3d.mm"
include "neg11d.mm"
include "pm2.61dane.mm"

theorem isosctrlem2
  let cA: class A


  assert |- ( ( A e. CC /\ ( abs ` A ) = 1 /\ -. 1 = A ) -> ( Im ` ( log ` ( 1 - A ) ) ) = ( Im ` ( log ` ( -u A / ( 1 - A ) ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
    #
    c1
    wceq
    #
    c1
    cA
    wceq
    #
    wn
    #
    w3a
    #
    c1
    cA
    cmin
    co
    #
    clog
    cfv
    #
    cim
    cfv
    #
    cA
    cneg
    #
    @6
    cdiv
    co
    #
    clog
    cfv
    #
    cim
    cfv
    #
    wceq
    @10
    cim
    cfv
    #
    cc0
    @5
    @13
    cc0
    wceq
    #
    wa
    #
    @8
    cc0
    @12
    @15
    @7
    @15
    @6
    @15
    c1
    @9
    caddc
    co
    @6
    crp
    @15
    c1
    cA
    @15
    1cnd
    #
    @0
    @2
    @4
    @14
    simpl1
    #
    negsubd
    @15
    c1
    @9
    c1
    crp
    wcel
    @15
    1rp
    a1i
    #
    @15
    c1
    @9
    crp
    @15
    @4
    c1
    @9
    wceq
    #
    @0
    @2
    @4
    @14
    simpl3
    @15
    @3
    @19
    @15
    @2
    @1
    cA
    wceq
    #
    @1
    @9
    wceq
    #
    wo
    @3
    @19
    wo
    @0
    @2
    @4
    @14
    simpl2
    @15
    cA
    @15
    cA
    @17
    @15
    @6
    c1
    cmin
    co
    #
    @9
    cr
    @15
    @22
    c1
    c1
    cmin
    co
    #
    cA
    cmin
    co
    #
    @9
    @15
    c1
    cA
    c1
    @16
    @17
    @16
    sub32d
    @24
    cc0
    cA
    cmin
    co
    @9
    @23
    cc0
    cA
    cmin
    1m1e0
    oveq1i
    cA
    df-neg
    eqtr4i
    syl6eq
    @15
    @6
    c1
    @15
    c1
    c1
    @6
    cdiv
    co
    #
    cdiv
    co
    @6
    cr
    @15
    @6
    @5
    @6
    cc
    wcel
    #
    @14
    @5
    c1
    cA
    @5
    1cnd
    #
    @0
    @2
    @4
    simp1
    #
    subcld
    #
    adantr
    @5
    @6
    cc0
    wne
    #
    @14
    @0
    @4
    @30
    @2
    @0
    @4
    wa
    @6
    cc0
    @0
    @6
    cc0
    wceq
    #
    @3
    @0
    @31
    @3
    c1
    cc
    wcel
    #
    @0
    @31
    @3
    wb
    ax-1cn
    c1
    cA
    subeq0
    mpan
    biimpd
    con3dimp
    neqned
    3adant2
    #
    adantr
    recrecd
    @15
    @25
    @15
    c1
    cneg
    #
    @6
    cneg
    #
    cdiv
    co
    #
    @25
    cr
    @5
    @36
    @25
    wceq
    @14
    @5
    c1
    @6
    @27
    @29
    @33
    div2negd
    #
    adantr
    @15
    @10
    ccj
    cfv
    #
    @36
    cr
    @5
    @38
    @36
    wceq
    @14
    @5
    @38
    c1
    cA
    cdiv
    co
    #
    cneg
    #
    c1
    @39
    cmin
    co
    #
    cdiv
    co
    #
    @34
    cA
    c1
    cmin
    co
    #
    cdiv
    co
    #
    @36
    @5
    @38
    @9
    ccj
    cfv
    #
    @6
    ccj
    cfv
    #
    cdiv
    co
    @40
    @46
    cdiv
    co
    @42
    @5
    @9
    @6
    @5
    cA
    @28
    negcld
    #
    @29
    @33
    cjdivd
    @5
    @45
    @40
    @46
    cdiv
    @5
    @45
    cA
    ccj
    cfv
    #
    cneg
    @40
    @5
    cA
    @28
    cjnegd
    @5
    @48
    @39
    @0
    @2
    @48
    @39
    wceq
    @4
    @0
    @2
    wa
    #
    @39
    @48
    @0
    @2
    cA
    cc0
    wceq
    #
    wn
    #
    @39
    @48
    wceq
    #
    @2
    @51
    @0
    @2
    @50
    c1
    cc0
    wceq
    #
    @50
    @2
    @1
    cc0
    wceq
    @53
    @50
    @1
    cc0
    cabs
    cfv
    cc0
    cA
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    @1
    c1
    cc0
    eqtr2
    sylan2
    c1
    cc0
    wne
    #
    @53
    wn
    @2
    @50
    wa
    ax-1ne0
    @54
    c1
    cc0
    @54
    id
    neneqd
    mp1i
    pm2.65da
    #
    adantl
    @51
    @0
    @2
    cA
    cc0
    wne
    #
    @52
    cA
    cc0
    df-ne
    @0
    @2
    @56
    w3a
    #
    @39
    cA
    @48
    cmul
    co
    #
    cA
    cdiv
    co
    @48
    @57
    c1
    @58
    cA
    cdiv
    @0
    @2
    c1
    @58
    wceq
    @56
    @49
    @1
    c2
    cexp
    co
    #
    c1
    @58
    @2
    @59
    c1
    wceq
    @0
    @2
    @59
    c1
    c2
    cexp
    co
    c1
    @1
    c1
    c2
    cexp
    oveq1
    sq1
    syl6eq
    adantl
    @0
    @59
    @58
    wceq
    @2
    cA
    absvalsq
    adantr
    eqtr3d
    3adant3
    oveq1d
    @57
    @48
    cA
    @57
    cA
    @0
    @2
    @56
    simp1
    #
    cjcld
    @60
    @0
    @2
    @56
    simp3
    divcan3d
    eqtrd
    syl3an3br
    mpd3an3
    eqcomd
    #
    3adant3
    negeqd
    eqtrd
    oveq1d
    @5
    @46
    @41
    @40
    cdiv
    @0
    @2
    @46
    @41
    wceq
    @4
    @49
    @46
    c1
    @48
    cmin
    co
    #
    @41
    @0
    @46
    @62
    wceq
    @2
    @0
    @46
    c1
    ccj
    cfv
    #
    @48
    cmin
    co
    #
    @62
    @32
    @0
    @46
    @64
    wceq
    ax-1cn
    c1
    cA
    cjsub
    mpan
    @0
    @63
    c1
    @48
    cmin
    @0
    c1
    @0
    1red
    cjred
    oveq1d
    eqtrd
    adantr
    @49
    @48
    @39
    c1
    cmin
    @61
    oveq2d
    eqtrd
    3adant3
    #
    oveq2d
    3eqtrd
    @5
    @42
    @34
    cA
    cdiv
    co
    #
    @41
    cdiv
    co
    #
    cA
    @66
    cmul
    co
    #
    cA
    @41
    cmul
    co
    #
    cdiv
    co
    @44
    @5
    @0
    @56
    @42
    @67
    wceq
    @28
    @5
    cA
    cc0
    @2
    @0
    @51
    @4
    @55
    3ad2ant2
    neqned
    #
    @0
    @56
    wa
    #
    @40
    @66
    @41
    cdiv
    @71
    c1
    cA
    @71
    1cnd
    @0
    @56
    simpl
    @0
    @56
    simpr
    divnegd
    oveq1d
    syl2anc
    @5
    @66
    @41
    cA
    @5
    @34
    cA
    @5
    c1
    @27
    negcld
    #
    @28
    @70
    divcld
    @5
    c1
    @39
    @27
    @5
    cA
    @28
    @70
    reccld
    #
    subcld
    @28
    @5
    @46
    @41
    cc0
    @65
    @5
    @6
    @29
    @33
    cjne0d
    eqnetrrd
    @70
    divcan5d
    @5
    @68
    @34
    @69
    @43
    cdiv
    @5
    @34
    cA
    @72
    @28
    @70
    divcan2d
    @5
    @69
    cA
    c1
    cmul
    co
    #
    cA
    @39
    cmul
    co
    #
    cmin
    co
    @43
    @5
    cA
    c1
    @39
    @28
    @27
    @73
    subdid
    @5
    @74
    cA
    @75
    c1
    cmin
    @5
    cA
    @28
    mulid1d
    @5
    cA
    @28
    @70
    recidd
    oveq12d
    eqtrd
    oveq12d
    3eqtr2d
    @5
    @43
    @35
    @34
    cdiv
    @5
    @0
    @32
    @43
    @35
    wceq
    @28
    @27
    @0
    @32
    wa
    #
    @43
    cneg
    #
    cneg
    @43
    @35
    @76
    @43
    cA
    c1
    subcl
    negnegd
    @76
    @77
    @6
    cA
    c1
    negsubdi2
    negeqd
    eqtr3d
    syl2anc
    oveq2d
    3eqtrd
    #
    adantr
    @15
    @38
    @10
    cr
    @15
    @10
    @15
    @10
    @5
    @10
    cc
    wcel
    #
    @14
    @5
    @9
    @6
    @47
    @29
    @33
    divcld
    #
    adantr
    @5
    @14
    simpr
    reim0bd
    #
    cjred
    @81
    eqeltrd
    eqeltrrd
    eqeltrrd
    @5
    @25
    cc0
    wne
    @14
    @5
    @6
    @29
    @33
    recne0d
    #
    adantr
    rereccld
    eqeltrrd
    @15
    1red
    resubcld
    eqeltrrd
    negrebd
    absord
    @2
    @20
    @3
    @21
    @19
    @2
    @20
    @3
    @1
    c1
    cA
    eqeq1
    biimpd
    @2
    @21
    @19
    @1
    c1
    @9
    eqeq1
    biimpd
    orim12d
    sylc
    ord
    mpd
    @18
    eqeltrrd
    #
    rpaddcld
    eqeltrrd
    #
    relogcld
    reim0d
    @15
    @11
    @15
    @10
    @15
    @9
    @6
    @83
    @84
    rpdivcld
    relogcld
    reim0d
    eqtr4d
    @5
    @13
    cc0
    wne
    #
    wa
    #
    @8
    @12
    @86
    @8
    @86
    @7
    @5
    @7
    cc
    wcel
    @85
    @5
    @6
    @29
    @33
    logcld
    adantr
    #
    imcld
    recnd
    @86
    @12
    @86
    @11
    @86
    @10
    @5
    @79
    @85
    @80
    adantr
    @5
    @10
    cc0
    wne
    @85
    @5
    @9
    @6
    @47
    @29
    @5
    cA
    @28
    @70
    negne0d
    @33
    divne0d
    adantr
    logcld
    #
    imcld
    recnd
    @86
    @7
    cneg
    #
    cim
    cfv
    @11
    ccj
    cfv
    #
    cim
    cfv
    @8
    cneg
    @12
    cneg
    @86
    @89
    @90
    cim
    @86
    @38
    clog
    cfv
    #
    @36
    clog
    cfv
    #
    @90
    @89
    @5
    @91
    @92
    wceq
    @85
    @5
    @38
    @36
    clog
    @78
    fveq2d
    adantr
    @5
    @79
    @85
    @91
    @90
    wceq
    @80
    @10
    logcj
    sylan
    @5
    @92
    @89
    wceq
    @85
    @5
    @25
    clog
    cfv
    #
    cneg
    #
    cneg
    @93
    @89
    @92
    @5
    @93
    @5
    @25
    @5
    @6
    @29
    @33
    reccld
    @82
    logcld
    negnegd
    @5
    @7
    @94
    @5
    @26
    @30
    @8
    cpi
    wne
    @7
    @94
    wceq
    @29
    @33
    cA
    isosctrlem1
    @6
    logrec
    syl3anc
    negeqd
    @5
    @36
    @25
    clog
    @37
    fveq2d
    3eqtr4rd
    adantr
    3eqtr3rd
    fveq2d
    @86
    @7
    @87
    imnegd
    @86
    @11
    @88
    imcjd
    3eqtr3d
    neg11d
    pm2.61dane
end
