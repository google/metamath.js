include "com.mm"
include "wcel.mm"
include "c0.mm"
include "crdg.mm"
include "cfv.mm"
include "csuc.mm"
include "cr1.mm"
include "cres.mm"
include "cv.mm"
include "wceq.mm"
include "fveq2.mm"
include "suceq.mm"
include "fveq2d.mm"
include "reseq12d.mm"
include "eqeq12d.mm"
include "weq.mm"
include "res0.mm"
include "r10.mm"
include "reseq2i.mm"
include "0ex.mm"
include "rdg0.mm"
include "3eqtr4ri.mm"
include "wa.mm"
include "wfn.mm"
include "ccrd.mm"
include "wf1o.mm"
include "peano2.mm"
include "ackbij2lem2.mm"
include "syl.mm"
include "f1ofn.mm"
include "adantr.mm"
include "wss.mm"
include "4syl.mm"
include "con0.mm"
include "nnon.mm"
include "r1sssuc.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "cima.mm"
include "cpw.mm"
include "r1suc.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "elpwid.mm"
include "resima2.mm"
include "cdm.mm"
include "cmpt.mm"
include "cvv.mm"
include "fvex.mm"
include "resex.mm"
include "dmeq.mm"
include "pweqd.mm"
include "imaeq1.mm"
include "mpteq12dv.mm"
include "dmex.mm"
include "pwex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "fveq1i.mm"
include "fndm.mm"
include "eleqtrrd.mm"
include "imaeq2.mm"
include "eqid.mm"
include "syl5eq.mm"
include "wtr.mm"
include "r1tr.mm"
include "a1i.mm"
include "dftr4.mm"
include "sylib.mm"
include "sselda.mm"
include "f1odm.mm"
include "3eqtr4d.mm"
include "adantlr.mm"
include "fveq1d.mm"
include "ad2antlr.mm"
include "rdgsuc.mm"
include "ad2antrr.mm"
include "3eqtr4rd.mm"
include "fvres.mm"
include "adantl.mm"
include "eqfnfvd.mm"
include "ex.mm"
include "finds.mm"
include "resss.mm"
include "syl6eqss.mm"

theorem ackbij2lem3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cH: class H
  let cB: class B
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )
  assume ackbij.g: |- G = ( x e. _V |-> ( y e. ~P dom x |-> ( F ` ( x " y ) ) ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint A x
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B x
  disjoint B y
  assert |- ( A e. _om -> ( rec ( G , (/) ) ` A ) C_ ( rec ( G , (/) ) ` suc A ) )

  proof
    cA
    com
    wcel
    cA
    cG
    c0
    crdg
    #
    cfv
    #
    cA
    csuc
    #
    @0
    cfv
    #
    cA
    cr1
    cfv
    #
    cres
    #
    @3
    va
    cv
    #
    @0
    cfv
    #
    @6
    csuc
    #
    @0
    cfv
    #
    @6
    cr1
    cfv
    #
    cres
    #
    wceq
    c0
    @0
    cfv
    #
    c0
    csuc
    #
    @0
    cfv
    #
    c0
    cr1
    cfv
    #
    cres
    #
    wceq
    vb
    cv
    #
    @0
    cfv
    #
    @17
    csuc
    #
    @0
    cfv
    #
    @17
    cr1
    cfv
    #
    cres
    #
    wceq
    #
    @20
    @19
    csuc
    #
    @0
    cfv
    #
    @19
    cr1
    cfv
    #
    cres
    #
    wceq
    #
    @1
    @5
    wceq
    va
    vb
    cA
    @6
    c0
    wceq
    #
    @7
    @12
    @11
    @16
    @6
    c0
    @0
    fveq2
    @29
    @9
    @14
    @10
    @15
    @29
    @8
    @13
    @0
    @6
    c0
    suceq
    fveq2d
    @6
    c0
    cr1
    fveq2
    reseq12d
    eqeq12d
    va
    vb
    weq
    #
    @7
    @18
    @11
    @22
    @6
    @17
    @0
    fveq2
    @30
    @9
    @20
    @10
    @21
    @30
    @8
    @19
    @0
    @6
    @17
    suceq
    fveq2d
    @6
    @17
    cr1
    fveq2
    reseq12d
    eqeq12d
    @6
    @19
    wceq
    #
    @7
    @20
    @11
    @27
    @6
    @19
    @0
    fveq2
    @31
    @9
    @25
    @10
    @26
    @31
    @8
    @24
    @0
    @6
    @19
    suceq
    fveq2d
    @6
    @19
    cr1
    fveq2
    reseq12d
    eqeq12d
    @6
    cA
    wceq
    #
    @7
    @1
    @11
    @5
    @6
    cA
    @0
    fveq2
    @32
    @9
    @3
    @10
    @4
    @32
    @8
    @2
    @0
    @6
    cA
    suceq
    fveq2d
    @6
    cA
    cr1
    fveq2
    reseq12d
    eqeq12d
    @14
    c0
    cres
    c0
    @16
    @12
    @14
    res0
    @15
    c0
    @14
    r10
    reseq2i
    c0
    cG
    0ex
    rdg0
    3eqtr4ri
    @17
    com
    wcel
    #
    @23
    @28
    @33
    @23
    wa
    #
    vc
    @26
    @20
    @27
    @33
    @20
    @26
    wfn
    #
    @23
    @33
    @26
    @26
    ccrd
    cfv
    #
    @20
    wf1o
    #
    @35
    @33
    @19
    com
    wcel
    #
    @37
    @17
    peano2
    #
    vx
    vy
    @19
    cF
    cG
    ackbij.f
    ackbij.g
    ackbij2lem2
    syl
    #
    @26
    @36
    @20
    f1ofn
    syl
    #
    adantr
    @33
    @27
    @26
    wfn
    #
    @23
    @33
    @25
    @24
    cr1
    cfv
    #
    wfn
    #
    @26
    @43
    wss
    #
    @42
    @33
    @38
    @24
    com
    wcel
    @43
    @43
    ccrd
    cfv
    #
    @25
    wf1o
    @44
    @39
    @19
    peano2
    vx
    vy
    @24
    cF
    cG
    ackbij.f
    ackbij.g
    ackbij2lem2
    @43
    @46
    @25
    f1ofn
    4syl
    @33
    @19
    con0
    wcel
    #
    @45
    @33
    @38
    @47
    @39
    @19
    nnon
    syl
    #
    @19
    r1sssuc
    syl
    @43
    @26
    @25
    fnssres
    syl2anc
    adantr
    @34
    vc
    cv
    #
    @26
    wcel
    #
    wa
    #
    @49
    @25
    cfv
    #
    @49
    @18
    cG
    cfv
    #
    cfv
    #
    @49
    @27
    cfv
    #
    @49
    @20
    cfv
    #
    @51
    @49
    @22
    cG
    cfv
    #
    cfv
    #
    @49
    @20
    cG
    cfv
    #
    cfv
    #
    @54
    @52
    @33
    @50
    @58
    @60
    wceq
    @23
    @33
    @50
    wa
    #
    @22
    @49
    cima
    #
    cF
    cfv
    #
    @20
    @49
    cima
    #
    cF
    cfv
    #
    @58
    @60
    @61
    @62
    @64
    cF
    @61
    @49
    @21
    wss
    @62
    @64
    wceq
    @61
    @49
    @21
    @33
    @50
    @49
    @21
    cpw
    #
    wcel
    @33
    @26
    @66
    @49
    @33
    @17
    con0
    wcel
    #
    @26
    @66
    wceq
    @17
    nnon
    #
    @17
    r1suc
    syl
    eleq2d
    biimpa
    #
    elpwid
    @20
    @49
    @21
    resima2
    syl
    fveq2d
    @61
    @58
    @49
    vy
    @22
    cdm
    #
    cpw
    #
    @22
    vy
    cv
    #
    cima
    #
    cF
    cfv
    #
    cmpt
    #
    cfv
    #
    @63
    @49
    @57
    @75
    @22
    cvv
    wcel
    @57
    @75
    wceq
    @20
    @21
    @19
    @0
    fvex
    #
    resex
    #
    vx
    @22
    vy
    vx
    cv
    #
    cdm
    #
    cpw
    #
    @79
    @72
    cima
    #
    cF
    cfv
    #
    cmpt
    #
    @75
    cvv
    cG
    @79
    @22
    wceq
    #
    vy
    @81
    @83
    @71
    @74
    @85
    @80
    @70
    @79
    @22
    dmeq
    pweqd
    @85
    @82
    @73
    cF
    @79
    @22
    @72
    imaeq1
    fveq2d
    mpteq12dv
    ackbij.g
    vy
    @71
    @74
    @70
    @22
    @78
    dmex
    pwex
    mptex
    fvmpt
    ax-mp
    fveq1i
    @61
    @49
    @71
    wcel
    @76
    @63
    wceq
    @61
    @49
    @66
    @71
    @69
    @33
    @71
    @66
    wceq
    @50
    @33
    @70
    @21
    @33
    @22
    @21
    wfn
    #
    @70
    @21
    wceq
    @33
    @35
    @21
    @26
    wss
    #
    @86
    @41
    @33
    @67
    @87
    @68
    @17
    r1sssuc
    syl
    @26
    @21
    @20
    fnssres
    syl2anc
    @21
    @22
    fndm
    syl
    pweqd
    adantr
    eleqtrrd
    vy
    @49
    @74
    @63
    @71
    @75
    vy
    vc
    weq
    #
    @73
    @62
    cF
    @72
    @49
    @22
    imaeq2
    fveq2d
    @75
    eqid
    @62
    cF
    fvex
    fvmpt
    syl
    syl5eq
    @61
    @60
    @49
    vy
    @20
    cdm
    #
    cpw
    #
    @20
    @72
    cima
    #
    cF
    cfv
    #
    cmpt
    #
    cfv
    #
    @65
    @49
    @59
    @93
    @20
    cvv
    wcel
    @59
    @93
    wceq
    @77
    vx
    @20
    @84
    @93
    cvv
    cG
    @79
    @20
    wceq
    #
    vy
    @81
    @83
    @90
    @92
    @95
    @80
    @89
    @79
    @20
    dmeq
    pweqd
    @95
    @82
    @91
    cF
    @79
    @20
    @72
    imaeq1
    fveq2d
    mpteq12dv
    ackbij.g
    vy
    @90
    @92
    @89
    @20
    @77
    dmex
    pwex
    mptex
    fvmpt
    ax-mp
    fveq1i
    @61
    @49
    @90
    wcel
    @94
    @65
    wceq
    @61
    @49
    @26
    cpw
    #
    @90
    @33
    @26
    @96
    @49
    @33
    @26
    wtr
    #
    @26
    @96
    wss
    @97
    @33
    @19
    r1tr
    a1i
    @26
    dftr4
    sylib
    sselda
    @33
    @90
    @96
    wceq
    @50
    @33
    @89
    @26
    @33
    @37
    @89
    @26
    wceq
    @40
    @26
    @36
    @20
    f1odm
    syl
    pweqd
    adantr
    eleqtrrd
    vy
    @49
    @92
    @65
    @90
    @93
    @88
    @91
    @64
    cF
    @72
    @49
    @20
    imaeq2
    fveq2d
    @93
    eqid
    @64
    cF
    fvex
    fvmpt
    syl
    syl5eq
    3eqtr4d
    adantlr
    @23
    @54
    @58
    wceq
    @33
    @50
    @23
    @49
    @53
    @57
    @18
    @22
    cG
    fveq2
    fveq1d
    ad2antlr
    @33
    @52
    @60
    wceq
    @23
    @50
    @33
    @49
    @25
    @59
    @33
    @47
    @25
    @59
    wceq
    @48
    c0
    @19
    cG
    rdgsuc
    syl
    fveq1d
    ad2antrr
    3eqtr4rd
    @50
    @55
    @52
    wceq
    @34
    @49
    @26
    @25
    fvres
    adantl
    @33
    @56
    @54
    wceq
    @23
    @50
    @33
    @49
    @20
    @53
    @33
    @67
    @20
    @53
    wceq
    @68
    c0
    @17
    cG
    rdgsuc
    syl
    fveq1d
    ad2antrr
    3eqtr4rd
    eqfnfvd
    ex
    finds
    @3
    @4
    resss
    syl6eqss
end
