include "cicc.mm"
include "co.mm"
include "cxp.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmpt2.mm"
include "ctx.mm"
include "cuni.mm"
include "eqid.mm"
include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "crest.mm"
include "cr.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "sseldd.mm"
include "icccld.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "cun.mm"
include "ssun1.mm"
include "wceq.mm"
include "iccsplit.mm"
include "syl3anc.mm"
include "syl5sseqr.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "restcldi.mm"
include "ctopon.mm"
include "toponuni.mm"
include "syl.mm"
include "ctop.mm"
include "topontop.mm"
include "topcld.mm"
include "3syl.mm"
include "eqeltrd.mm"
include "txcld.mm"
include "ssun2.mm"
include "xpeq1d.mm"
include "xpundir.mm"
include "syl6eq.mm"
include "retopon.mm"
include "eqeltri.mm"
include "resttopon.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "txtopon.mm"
include "eqtr3d.mm"
include "wf.mm"
include "wral.mm"
include "ccn.mm"
include "sstrd.mm"
include "cntop2.mm"
include "toptopon.mm"
include "sylib.mm"
include "w3a.mm"
include "wa.mm"
include "wb.mm"
include "elicc2.mm"
include "biimpa.mm"
include "simp3d.mm"
include "3adant3.mm"
include "iftrued.mm"
include "mpt2eq3dva.mm"
include "cnf2.mm"
include "fmpt2.mm"
include "sylibr.mm"
include "simp2d.mm"
include "biantrud.mm"
include "simp1d.mm"
include "adantr.mm"
include "letri3d.mm"
include "bitr4d.mm"
include "wi.mm"
include "ancom2s.mm"
include "ifeq1d.mm"
include "ifid.mm"
include "expr.mm"
include "3adant2.mm"
include "sylbid.mm"
include "iffalse.mm"
include "pm2.61d1.mm"
include "ralun.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "feq2d.mm"
include "mpbid.mm"
include "cres.mm"
include "ssid.mm"
include "resmpt2.mm"
include "sylancl.mm"
include "cvv.mm"
include "retop.mm"
include "ovex.mm"
include "resttop.mm"
include "mp2an.mm"
include "a1i.mm"
include "ovexd.mm"
include "txrest.mm"
include "syl22anc.mm"
include "restabs.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"
include "oveq2d.mm"
include "restid.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "3eltr4d.mm"
include "paste.mm"

theorem cnmpt2pc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cE: class E
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  assume cnmpt2pc.r: |- R = ( topGen ` ran (,) )
  assume cnmpt2pc.m: |- M = ( R |`t ( A [,] B ) )
  assume cnmpt2pc.n: |- N = ( R |`t ( B [,] C ) )
  assume cnmpt2pc.o: |- O = ( R |`t ( A [,] C ) )
  assume cnmpt2pc.a: |- ( ph -> A e. RR )
  assume cnmpt2pc.c: |- ( ph -> C e. RR )
  assume cnmpt2pc.b: |- ( ph -> B e. ( A [,] C ) )
  assume cnmpt2pc.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt2pc.q: |- ( ( ph /\ ( x = B /\ y e. X ) ) -> D = E )
  assume cnmpt2pc.d: |- ( ph -> ( x e. ( A [,] B ) , y e. X |-> D ) e. ( ( M tX J ) Cn K ) )
  assume cnmpt2pc.e: |- ( ph -> ( x e. ( B [,] C ) , y e. X |-> E ) e. ( ( N tX J ) Cn K ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  assert |- ( ph -> ( x e. ( A [,] C ) , y e. X |-> if ( x <_ B , D , E ) ) e. ( ( O tX J ) Cn K ) )

  proof
    wph
    cA
    cB
    cicc
    co
    #
    cX
    cxp
    #
    cB
    cC
    cicc
    co
    #
    cX
    cxp
    #
    vx
    vy
    cA
    cC
    cicc
    co
    #
    cX
    vx
    cv
    #
    cB
    cle
    wbr
    #
    cD
    cE
    cif
    #
    cmpt2
    #
    cO
    cJ
    ctx
    co
    #
    cK
    @9
    cuni
    #
    cK
    cuni
    #
    @10
    eqid
    @11
    eqid
    #
    wph
    @0
    cO
    ccld
    cfv
    #
    wcel
    cX
    cJ
    ccld
    cfv
    #
    wcel
    #
    @1
    @9
    ccld
    cfv
    #
    wcel
    wph
    @0
    cR
    @4
    crest
    co
    #
    ccld
    cfv
    #
    @13
    wph
    @4
    cr
    wss
    #
    @0
    cR
    ccld
    cfv
    #
    wcel
    @0
    @4
    wss
    #
    @0
    @18
    wcel
    wph
    cA
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    @19
    cnmpt2pc.a
    cnmpt2pc.c
    cA
    cC
    iccssre
    syl2anc
    #
    wph
    @0
    cioo
    crn
    ctg
    cfv
    #
    ccld
    cfv
    #
    @20
    wph
    @22
    cB
    cr
    wcel
    #
    @0
    @26
    wcel
    cnmpt2pc.a
    wph
    @4
    cr
    cB
    @24
    cnmpt2pc.b
    sseldd
    #
    cA
    cB
    icccld
    syl2anc
    cR
    @25
    ccld
    cnmpt2pc.r
    fveq2i
    #
    syl6eleqr
    wph
    @0
    @2
    cun
    #
    @0
    @4
    @0
    @2
    ssun1
    wph
    @22
    @23
    cB
    @4
    wcel
    @4
    @30
    wceq
    cnmpt2pc.a
    cnmpt2pc.c
    cnmpt2pc.b
    cA
    cC
    cB
    iccsplit
    syl3anc
    #
    syl5sseqr
    #
    @4
    @0
    cR
    cr
    cr
    @25
    cuni
    cR
    cuni
    uniretop
    cR
    @25
    cnmpt2pc.r
    unieqi
    eqtr4i
    #
    restcldi
    syl3anc
    cO
    @17
    ccld
    cnmpt2pc.o
    fveq2i
    #
    syl6eleqr
    wph
    cX
    cJ
    cuni
    #
    @14
    wph
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cX
    @35
    wceq
    cnmpt2pc.j
    cX
    cJ
    toponuni
    syl
    #
    wph
    @37
    cJ
    ctop
    wcel
    @35
    @14
    wcel
    cnmpt2pc.j
    cX
    cJ
    topontop
    cJ
    @35
    @35
    eqid
    #
    topcld
    3syl
    eqeltrd
    #
    @0
    cX
    cO
    cJ
    txcld
    syl2anc
    wph
    @2
    @13
    wcel
    @15
    @3
    @16
    wcel
    wph
    @2
    @18
    @13
    wph
    @19
    @2
    @20
    wcel
    @2
    @4
    wss
    #
    @2
    @18
    wcel
    @24
    wph
    @2
    @26
    @20
    wph
    @27
    @23
    @2
    @26
    wcel
    @28
    cnmpt2pc.c
    cB
    cC
    icccld
    syl2anc
    @29
    syl6eleqr
    wph
    @30
    @2
    @4
    @2
    @0
    ssun2
    @31
    syl5sseqr
    #
    @4
    @2
    cR
    cr
    @33
    restcldi
    syl3anc
    @34
    syl6eleqr
    @40
    @2
    cX
    cO
    cJ
    txcld
    syl2anc
    wph
    @4
    cX
    cxp
    #
    @1
    @3
    cun
    #
    @10
    wph
    @43
    @30
    cX
    cxp
    @44
    wph
    @4
    @30
    cX
    @31
    xpeq1d
    @0
    @2
    cX
    xpundir
    syl6eq
    wph
    @9
    @43
    ctopon
    cfv
    wcel
    #
    @43
    @10
    wceq
    wph
    cO
    @4
    ctopon
    cfv
    #
    wcel
    @37
    @45
    wph
    cO
    @17
    @46
    cnmpt2pc.o
    wph
    cR
    cr
    ctopon
    cfv
    #
    wcel
    #
    @19
    @17
    @46
    wcel
    cR
    @25
    @47
    cnmpt2pc.r
    retopon
    eqeltri
    #
    @24
    @4
    cR
    cr
    resttopon
    sylancr
    syl5eqel
    cnmpt2pc.j
    cO
    cJ
    @4
    cX
    txtopon
    syl2anc
    @43
    @9
    toponuni
    syl
    #
    eqtr3d
    wph
    @43
    @11
    @8
    wf
    #
    @10
    @11
    @8
    wf
    wph
    @7
    @11
    wcel
    vy
    cX
    wral
    #
    vx
    @4
    wral
    #
    @51
    wph
    @53
    @52
    vx
    @30
    wral
    #
    wph
    @52
    vx
    @0
    wral
    #
    @52
    vx
    @2
    wral
    #
    @54
    wph
    @1
    @11
    vx
    vy
    @0
    cX
    @7
    cmpt2
    #
    wf
    #
    @55
    wph
    cM
    cJ
    ctx
    co
    #
    @1
    ctopon
    cfv
    wcel
    #
    cK
    @11
    ctopon
    cfv
    wcel
    #
    @57
    @59
    cK
    ccn
    co
    #
    wcel
    @58
    wph
    cM
    @0
    ctopon
    cfv
    #
    wcel
    @37
    @60
    wph
    cM
    cR
    @0
    crest
    co
    #
    @63
    cnmpt2pc.m
    wph
    @48
    @0
    cr
    wss
    @64
    @63
    wcel
    @49
    wph
    @0
    @4
    cr
    @32
    @24
    sstrd
    @0
    cR
    cr
    resttopon
    sylancr
    syl5eqel
    cnmpt2pc.j
    cM
    cJ
    @0
    cX
    txtopon
    syl2anc
    wph
    cK
    ctop
    wcel
    #
    @61
    wph
    vx
    vy
    @0
    cX
    cD
    cmpt2
    #
    @62
    wcel
    @65
    cnmpt2pc.d
    @66
    @59
    cK
    cntop2
    syl
    cK
    @11
    @12
    toptopon
    sylib
    #
    wph
    @57
    @66
    @62
    wph
    vx
    vy
    @0
    cX
    @7
    cD
    wph
    @5
    @0
    wcel
    #
    vy
    cv
    cX
    wcel
    #
    w3a
    @6
    cD
    cE
    wph
    @68
    @6
    @69
    wph
    @68
    wa
    @5
    cr
    wcel
    #
    cA
    @5
    cle
    wbr
    #
    @6
    wph
    @68
    @70
    @71
    @6
    w3a
    #
    wph
    @22
    @27
    @68
    @72
    wb
    cnmpt2pc.a
    @28
    cA
    cB
    @5
    elicc2
    syl2anc
    biimpa
    simp3d
    3adant3
    iftrued
    mpt2eq3dva
    cnmpt2pc.d
    eqeltrd
    #
    @57
    @59
    cK
    @1
    @11
    cnf2
    syl3anc
    vx
    vy
    @0
    cX
    @7
    @11
    @57
    @57
    eqid
    fmpt2
    sylibr
    wph
    @3
    @11
    vx
    vy
    @2
    cX
    @7
    cmpt2
    #
    wf
    #
    @56
    wph
    cN
    cJ
    ctx
    co
    #
    @3
    ctopon
    cfv
    wcel
    #
    @61
    @74
    @76
    cK
    ccn
    co
    #
    wcel
    @75
    wph
    cN
    @2
    ctopon
    cfv
    #
    wcel
    @37
    @77
    wph
    cN
    cR
    @2
    crest
    co
    #
    @79
    cnmpt2pc.n
    wph
    @48
    @2
    cr
    wss
    @80
    @79
    wcel
    @49
    wph
    @2
    @4
    cr
    @42
    @24
    sstrd
    @2
    cR
    cr
    resttopon
    sylancr
    syl5eqel
    cnmpt2pc.j
    cN
    cJ
    @2
    cX
    txtopon
    syl2anc
    @67
    wph
    @74
    vx
    vy
    @2
    cX
    cE
    cmpt2
    @78
    wph
    vx
    vy
    @2
    cX
    @7
    cE
    wph
    @5
    @2
    wcel
    #
    @69
    w3a
    #
    @6
    @7
    cE
    wceq
    #
    @82
    @6
    @5
    cB
    wceq
    #
    @83
    wph
    @81
    @6
    @84
    wb
    @69
    wph
    @81
    wa
    #
    @6
    @6
    cB
    @5
    cle
    wbr
    #
    wa
    @84
    @85
    @86
    @6
    @85
    @70
    @86
    @5
    cC
    cle
    wbr
    #
    wph
    @81
    @70
    @86
    @87
    w3a
    #
    wph
    @27
    @23
    @81
    @88
    wb
    @28
    cnmpt2pc.c
    cB
    cC
    @5
    elicc2
    syl2anc
    biimpa
    #
    simp2d
    biantrud
    @85
    @5
    cB
    @85
    @70
    @86
    @87
    @89
    simp1d
    wph
    @27
    @81
    @28
    adantr
    letri3d
    bitr4d
    3adant3
    wph
    @69
    @84
    @83
    wi
    @81
    wph
    @69
    @84
    @83
    wph
    @69
    @84
    wa
    wa
    #
    @7
    @6
    cE
    cE
    cif
    cE
    @90
    @6
    cD
    cE
    cE
    wph
    @84
    @69
    cD
    cE
    wceq
    cnmpt2pc.q
    ancom2s
    ifeq1d
    @6
    cE
    ifid
    syl6eq
    expr
    3adant2
    sylbid
    @6
    cD
    cE
    iffalse
    pm2.61d1
    mpt2eq3dva
    cnmpt2pc.e
    eqeltrd
    #
    @74
    @76
    cK
    @3
    @11
    cnf2
    syl3anc
    vx
    vy
    @2
    cX
    @7
    @11
    @74
    @74
    eqid
    fmpt2
    sylibr
    @52
    vx
    @0
    @2
    ralun
    syl2anc
    wph
    @52
    vx
    @4
    @30
    @31
    raleqdv
    mpbird
    vx
    vy
    @4
    cX
    @7
    @11
    @8
    @8
    eqid
    fmpt2
    sylib
    wph
    @43
    @10
    @11
    @8
    @50
    feq2d
    mpbid
    wph
    @57
    @62
    @8
    @1
    cres
    #
    @9
    @1
    crest
    co
    #
    cK
    ccn
    co
    @73
    wph
    @21
    cX
    cX
    wss
    #
    @92
    @57
    wceq
    @32
    cX
    ssid
    #
    vx
    vy
    @4
    cX
    @0
    cX
    @7
    resmpt2
    sylancl
    wph
    @93
    @59
    cK
    ccn
    wph
    @93
    cO
    @0
    crest
    co
    #
    cJ
    cX
    crest
    co
    #
    ctx
    co
    #
    @59
    wph
    cO
    ctop
    wcel
    #
    @37
    @0
    cvv
    wcel
    @15
    @93
    @98
    wceq
    @99
    wph
    cO
    @17
    ctop
    cnmpt2pc.o
    cR
    ctop
    wcel
    #
    @4
    cvv
    wcel
    #
    @17
    ctop
    wcel
    cR
    @25
    ctop
    cnmpt2pc.r
    retop
    eqeltri
    #
    cA
    cC
    cicc
    ovex
    @4
    cR
    cvv
    resttop
    mp2an
    eqeltri
    a1i
    #
    cnmpt2pc.j
    wph
    cA
    cB
    cicc
    ovexd
    @40
    @0
    cX
    cO
    cJ
    ctop
    @36
    cvv
    @14
    txrest
    syl22anc
    wph
    @96
    cM
    @97
    cJ
    ctx
    wph
    @17
    @0
    crest
    co
    #
    @64
    @96
    cM
    wph
    @100
    @21
    @101
    @104
    @64
    wceq
    @100
    wph
    @102
    a1i
    #
    @32
    wph
    cA
    cC
    cicc
    ovexd
    #
    @0
    @4
    cR
    ctop
    cvv
    restabs
    syl3anc
    cO
    @17
    @0
    crest
    cnmpt2pc.o
    oveq1i
    cnmpt2pc.m
    3eqtr4g
    wph
    @97
    cJ
    @35
    crest
    co
    #
    cJ
    wph
    cX
    @35
    cJ
    crest
    @38
    oveq2d
    wph
    @37
    @107
    cJ
    wceq
    cnmpt2pc.j
    cJ
    @36
    @35
    @39
    restid
    syl
    eqtrd
    #
    oveq12d
    eqtrd
    oveq1d
    3eltr4d
    wph
    @74
    @78
    @8
    @3
    cres
    #
    @9
    @3
    crest
    co
    #
    cK
    ccn
    co
    @91
    wph
    @41
    @94
    @109
    @74
    wceq
    @42
    @95
    vx
    vy
    @4
    cX
    @2
    cX
    @7
    resmpt2
    sylancl
    wph
    @110
    @76
    cK
    ccn
    wph
    @110
    cO
    @2
    crest
    co
    #
    @97
    ctx
    co
    #
    @76
    wph
    @99
    @37
    @2
    cvv
    wcel
    @15
    @110
    @112
    wceq
    @103
    cnmpt2pc.j
    wph
    cB
    cC
    cicc
    ovexd
    @40
    @2
    cX
    cO
    cJ
    ctop
    @36
    cvv
    @14
    txrest
    syl22anc
    wph
    @111
    cN
    @97
    cJ
    ctx
    wph
    @17
    @2
    crest
    co
    #
    @80
    @111
    cN
    wph
    @100
    @41
    @101
    @113
    @80
    wceq
    @105
    @42
    @106
    @2
    @4
    cR
    ctop
    cvv
    restabs
    syl3anc
    cO
    @17
    @2
    crest
    cnmpt2pc.o
    oveq1i
    cnmpt2pc.n
    3eqtr4g
    @108
    oveq12d
    eqtrd
    oveq1d
    3eltr4d
    paste
end
