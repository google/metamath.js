include "cat.mm"
include "wcel.mm"
include "wne.mm"
include "cv.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "w3a.mm"
include "wrex.mm"
include "c0v.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "chil.mm"
include "wi.mm"
include "atom1d.mm"
include "reeanv.mm"
include "an4.mm"
include "wb.mm"
include "neeq1.mm"
include "neeq2.mm"
include "sylan9bb.mm"
include "adantl.mm"
include "cva.mm"
include "hvaddcl.mm"
include "adantr.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "hvaddeq0.mm"
include "sneq.mm"
include "fveq2d.mm"
include "cc.mm"
include "cc0.mm"
include "neg1cn.mm"
include "neg1ne0.mm"
include "spansncol.mm"
include "mp3an23.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "sylbid.mm"
include "necon3d.mm"
include "imp.mm"
include "spansna.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "eqeq2.mm"
include "biimpd.mm"
include "spansneleqi.mm"
include "syl.mm"
include "elspansn.mm"
include "caddc.mm"
include "addcl.mm"
include "mpan2.mm"
include "ad2antlr.mm"
include "cmv.mm"
include "hvmulcl.mm"
include "ancoms.mm"
include "simpll.mm"
include "simplr.mm"
include "hvsubadd.mm"
include "syl3anc.mm"
include "biimpar.mm"
include "hvsubval.mm"
include "sylancom.mm"
include "ax-hvdistr2.mm"
include "mp3an2.mm"
include "eqtr4d.mm"
include "eqtr3d.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "syld.mm"
include "sylibrd.mm"
include "spansneleq.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "sylan9r.mm"
include "adantlrl.mm"
include "adantrr.mm"
include "adantll.mm"
include "ax-hvcom.mm"
include "eqeq1d.mm"
include "bitr4d.mm"
include "adantlrr.mm"
include "adantrl.mm"
include "cpr.mm"
include "spanpr.mm"
include "oveq12.mm"
include "cph.mm"
include "cun.mm"
include "df-pr.mm"
include "fveq2i.mm"
include "snssi.mm"
include "spanun.mm"
include "syl2an.mm"
include "syl5eq.mm"
include "cch.mm"
include "spansnch.mm"
include "spansnj.mm"
include "sylan.mm"
include "eqtr2d.mm"
include "sseqtr4d.mm"
include "sseq1.mm"
include "3anbi123d.mm"
include "syl13anc.mm"
include "expl.mm"
include "syl5bi.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"
include "3impia.mm"

theorem superpos
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vw: setvar w

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- ( ( A e. HAtoms /\ B e. HAtoms /\ A =/= B ) -> E. x e. HAtoms ( x =/= A /\ x =/= B /\ x C_ ( A vH B ) ) )

  proof
    cA
    cat
    wcel
    #
    cB
    cat
    wcel
    #
    cA
    cB
    wne
    #
    vx
    cv
    #
    cA
    wne
    #
    @3
    cB
    wne
    #
    @3
    cA
    cB
    chj
    co
    #
    wss
    #
    w3a
    #
    vx
    cat
    wrex
    #
    @0
    vy
    cv
    #
    c0v
    wne
    #
    cA
    @10
    csn
    #
    cspn
    cfv
    #
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    vz
    cv
    #
    c0v
    wne
    #
    cB
    @17
    csn
    #
    cspn
    cfv
    #
    wceq
    #
    wa
    #
    vz
    chil
    wrex
    #
    @2
    @9
    wi
    #
    @1
    vy
    cA
    atom1d
    vz
    cB
    atom1d
    @16
    @23
    wa
    @15
    @22
    wa
    #
    vz
    chil
    wrex
    vy
    chil
    wrex
    @24
    @15
    @22
    vy
    vz
    chil
    chil
    reeanv
    @25
    @24
    vy
    vz
    chil
    chil
    @25
    @11
    @18
    wa
    #
    @14
    @21
    wa
    #
    wa
    @10
    chil
    wcel
    #
    @17
    chil
    wcel
    #
    wa
    #
    @24
    @11
    @14
    @18
    @21
    an4
    @30
    @26
    @27
    @24
    @30
    @26
    wa
    #
    @27
    wa
    #
    @2
    @13
    @20
    wne
    #
    @9
    @27
    @2
    @33
    wb
    @31
    @14
    @2
    @13
    cB
    wne
    @21
    @33
    cA
    @13
    cB
    neeq1
    cB
    @20
    @13
    neeq2
    sylan9bb
    adantl
    @32
    @33
    @9
    @32
    @33
    wa
    @10
    @17
    cva
    co
    #
    csn
    cspn
    cfv
    #
    cat
    wcel
    #
    @35
    cA
    wne
    #
    @35
    cB
    wne
    #
    @35
    @6
    wss
    #
    @9
    @31
    @33
    @36
    @27
    @30
    @33
    @36
    @26
    @30
    @33
    wa
    @34
    chil
    wcel
    #
    @34
    c0v
    wne
    #
    @36
    @30
    @40
    @33
    @10
    @17
    hvaddcl
    #
    adantr
    @30
    @33
    @41
    @30
    @34
    c0v
    @13
    @20
    @30
    @34
    c0v
    wceq
    @10
    c1
    cneg
    #
    @17
    csm
    co
    #
    wceq
    #
    @13
    @20
    wceq
    #
    @10
    @17
    hvaddeq0
    @29
    @45
    @46
    wi
    @28
    @29
    @45
    @46
    @45
    @29
    @13
    @44
    csn
    #
    cspn
    cfv
    #
    @20
    @45
    @12
    @47
    cspn
    @10
    @44
    sneq
    fveq2d
    @29
    @43
    cc
    wcel
    #
    @43
    cc0
    wne
    @48
    @20
    wceq
    neg1cn
    neg1ne0
    @17
    @43
    spansncol
    mp3an23
    sylan9eqr
    ex
    adantl
    sylbid
    necon3d
    imp
    @34
    spansna
    syl2anc
    adantlr
    adantlr
    @32
    @33
    @37
    @31
    @14
    @33
    @37
    wi
    #
    @21
    @30
    @18
    @14
    @50
    @11
    @30
    @18
    wa
    #
    @14
    wa
    @35
    cA
    @13
    @20
    @14
    @35
    cA
    wceq
    #
    @35
    @13
    wceq
    #
    @51
    @46
    @14
    @52
    @53
    cA
    @13
    @35
    eqeq2
    biimpd
    @51
    @53
    @17
    @13
    wcel
    #
    @46
    @30
    @53
    @54
    wi
    @18
    @30
    @53
    @17
    vw
    cv
    #
    @10
    csm
    co
    #
    wceq
    #
    vw
    cc
    wrex
    #
    @54
    @30
    @53
    @34
    @13
    wcel
    #
    @58
    @30
    @40
    @53
    @59
    wi
    @42
    @34
    @10
    spansneleqi
    syl
    @30
    @59
    @34
    vv
    cv
    #
    @10
    csm
    co
    #
    wceq
    #
    vv
    cc
    wrex
    #
    @58
    @28
    @59
    @63
    wb
    @29
    vv
    @10
    @34
    elspansn
    adantr
    @30
    @62
    @58
    vv
    cc
    @30
    @60
    cc
    wcel
    #
    @62
    @58
    @30
    @64
    wa
    #
    @62
    wa
    #
    @60
    @43
    caddc
    co
    #
    cc
    wcel
    #
    @17
    @67
    @10
    csm
    co
    #
    wceq
    #
    @58
    @64
    @68
    @30
    @62
    @64
    @49
    @68
    neg1cn
    @60
    @43
    addcl
    mpan2
    #
    ad2antlr
    @66
    @61
    @10
    cmv
    co
    #
    @17
    @69
    @65
    @72
    @17
    wceq
    #
    @62
    @65
    @61
    chil
    wcel
    #
    @28
    @29
    @73
    @62
    wb
    @28
    @64
    @74
    @29
    @64
    @28
    @74
    @60
    @10
    hvmulcl
    #
    ancoms
    adantlr
    @28
    @29
    @64
    simpll
    #
    @28
    @29
    @64
    simplr
    #
    @61
    @10
    @17
    hvsubadd
    syl3anc
    biimpar
    @65
    @72
    @69
    wceq
    #
    @62
    @28
    @64
    @78
    @29
    @64
    @28
    @78
    @64
    @28
    wa
    @72
    @61
    @43
    @10
    csm
    co
    cva
    co
    #
    @69
    @64
    @28
    @74
    @72
    @79
    wceq
    @75
    @61
    @10
    hvsubval
    sylancom
    @64
    @49
    @28
    @69
    @79
    wceq
    neg1cn
    @60
    @43
    @10
    ax-hvdistr2
    mp3an2
    eqtr4d
    ancoms
    adantlr
    adantr
    eqtr3d
    @57
    @70
    vw
    @67
    cc
    @55
    @67
    wceq
    #
    @56
    @69
    @17
    @55
    @67
    @10
    csm
    oveq1
    eqeq2d
    rspcev
    syl2anc
    exp31
    rexlimdv
    sylbid
    syld
    @28
    @54
    @58
    wb
    @29
    vw
    @10
    @17
    elspansn
    adantr
    sylibrd
    adantr
    @28
    @18
    @54
    @46
    wi
    @29
    @28
    @18
    wa
    @54
    @20
    @13
    wceq
    @46
    @17
    @10
    spansneleq
    @20
    @13
    eqcom
    syl6ib
    adantlr
    syld
    sylan9r
    necon3d
    adantlrl
    adantrr
    imp
    @32
    @33
    @38
    @31
    @21
    @33
    @38
    wi
    #
    @14
    @30
    @11
    @21
    @81
    @18
    @30
    @11
    wa
    #
    @21
    wa
    @35
    cB
    @13
    @20
    @21
    @35
    cB
    wceq
    #
    @35
    @20
    wceq
    #
    @82
    @46
    @21
    @83
    @84
    cB
    @20
    @35
    eqeq2
    biimpd
    @82
    @84
    @10
    @20
    wcel
    #
    @46
    @30
    @84
    @85
    wi
    @11
    @30
    @84
    @10
    @55
    @17
    csm
    co
    #
    wceq
    #
    vw
    cc
    wrex
    #
    @85
    @30
    @84
    @34
    @20
    wcel
    #
    @88
    @30
    @40
    @84
    @89
    wi
    @42
    @34
    @17
    spansneleqi
    syl
    @30
    @89
    @34
    @60
    @17
    csm
    co
    #
    wceq
    #
    vv
    cc
    wrex
    #
    @88
    @29
    @89
    @92
    wb
    @28
    vv
    @17
    @34
    elspansn
    adantl
    @30
    @91
    @88
    vv
    cc
    @30
    @64
    @91
    @88
    @65
    @91
    wa
    #
    @68
    @10
    @67
    @17
    csm
    co
    #
    wceq
    #
    @88
    @64
    @68
    @30
    @91
    @71
    ad2antlr
    @93
    @90
    @17
    cmv
    co
    #
    @10
    @94
    @65
    @96
    @10
    wceq
    #
    @91
    @65
    @97
    @17
    @10
    cva
    co
    #
    @90
    wceq
    #
    @91
    @65
    @90
    chil
    wcel
    #
    @29
    @28
    @97
    @99
    wb
    @29
    @64
    @100
    @28
    @64
    @29
    @100
    @60
    @17
    hvmulcl
    #
    ancoms
    adantll
    @77
    @76
    @90
    @17
    @10
    hvsubadd
    syl3anc
    @65
    @34
    @98
    @90
    @30
    @34
    @98
    wceq
    @64
    @10
    @17
    ax-hvcom
    adantr
    eqeq1d
    bitr4d
    biimpar
    @65
    @96
    @94
    wceq
    #
    @91
    @29
    @64
    @102
    @28
    @64
    @29
    @102
    @64
    @29
    wa
    @96
    @90
    @44
    cva
    co
    #
    @94
    @64
    @29
    @100
    @96
    @103
    wceq
    @101
    @90
    @17
    hvsubval
    sylancom
    @64
    @49
    @29
    @94
    @103
    wceq
    neg1cn
    @60
    @43
    @17
    ax-hvdistr2
    mp3an2
    eqtr4d
    ancoms
    adantll
    adantr
    eqtr3d
    @87
    @95
    vw
    @67
    cc
    @80
    @86
    @94
    @10
    @55
    @67
    @17
    csm
    oveq1
    eqeq2d
    rspcev
    syl2anc
    exp31
    rexlimdv
    sylbid
    syld
    @29
    @85
    @88
    wb
    @28
    vw
    @17
    @10
    elspansn
    adantl
    sylibrd
    adantr
    @29
    @11
    @85
    @46
    wi
    @28
    @10
    @17
    spansneleq
    adantll
    syld
    sylan9r
    necon3d
    adantlrr
    adantrl
    imp
    @32
    @39
    @33
    @30
    @27
    @39
    @26
    @30
    @27
    wa
    @35
    @10
    @17
    cpr
    #
    cspn
    cfv
    #
    @6
    @30
    @35
    @105
    wss
    @27
    @10
    @17
    spanpr
    adantr
    @27
    @30
    @6
    @13
    @20
    chj
    co
    #
    @105
    cA
    @13
    cB
    @20
    chj
    oveq12
    @30
    @105
    @13
    @20
    cph
    co
    #
    @106
    @30
    @105
    @12
    @19
    cun
    #
    cspn
    cfv
    #
    @107
    @104
    @108
    cspn
    @10
    @17
    df-pr
    fveq2i
    @28
    @12
    chil
    wss
    @19
    chil
    wss
    @109
    @107
    wceq
    @29
    @10
    chil
    snssi
    @17
    chil
    snssi
    @12
    @19
    spanun
    syl2an
    syl5eq
    @28
    @13
    cch
    wcel
    @29
    @107
    @106
    wceq
    @10
    spansnch
    @13
    @17
    spansnj
    sylan
    eqtr2d
    sylan9eqr
    sseqtr4d
    adantlr
    adantr
    @8
    @37
    @38
    @39
    w3a
    vx
    @35
    cat
    @3
    @35
    wceq
    @4
    @37
    @5
    @38
    @7
    @39
    @3
    @35
    cA
    neeq1
    @3
    @35
    cB
    neeq1
    @3
    @35
    @6
    sseq1
    3anbi123d
    rspcev
    syl13anc
    ex
    sylbid
    expl
    syl5bi
    rexlimivv
    sylbir
    syl2anb
    3impia
end
