include "cv.mm"
include "cr1.mm"
include "cfv.mm"
include "ccrd.mm"
include "c0.mm"
include "crdg.mm"
include "wf1o.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "f1oeq123d.mm"
include "f1o0.mm"
include "wb.mm"
include "0ex.mm"
include "rdg0.mm"
include "f1oeq1.mm"
include "ax-mp.mm"
include "r10.mm"
include "fveq2i.mm"
include "card0.mm"
include "eqtri.mm"
include "f1oeq23.mm"
include "mp2an.mm"
include "bitri.mm"
include "mpbir.mm"
include "com.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "cres.mm"
include "cima.mm"
include "cmpt.mm"
include "ccom.mm"
include "cfn.mm"
include "cin.mm"
include "wf1.mm"
include "wss.mm"
include "ackbij1lem17.mm"
include "a1i.mm"
include "r1fin.mm"
include "ficardom.mm"
include "syl.mm"
include "ackbij2lem1.mm"
include "f1ores.mm"
include "syl2anc.mm"
include "ackbij1b.mm"
include "cen.mm"
include "wbr.mm"
include "ficardid.mm"
include "pwen.mm"
include "carden2b.mm"
include "4syl.mm"
include "eqtrd.mm"
include "f1oeq3d.mm"
include "mpbid.mm"
include "adantr.mm"
include "f1opw.mm"
include "adantl.mm"
include "f1oco.mm"
include "cdm.mm"
include "frsuc.mm"
include "peano2.mm"
include "fvresd.mm"
include "fvres.mm"
include "cvv.mm"
include "fvex.mm"
include "dmeq.mm"
include "pweqd.mm"
include "imaeq1.mm"
include "mpteq12dv.mm"
include "dmex.mm"
include "pwex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl6eq.mm"
include "3eqtr3d.mm"
include "f1odm.mm"
include "mpteq1d.mm"
include "wfn.mm"
include "eqid.mm"
include "fnmpti.mm"
include "f1ofn.mm"
include "wf.mm"
include "f1of.mm"
include "ffvelrnda.mm"
include "imaeq2.mm"
include "imaex.mm"
include "fvco3.mm"
include "sylan.mm"
include "3eqtr4rd.mm"
include "eqfnfvd.mm"
include "con0.mm"
include "nnon.mm"
include "r1suc.mm"
include "bitrd.mm"
include "mpbird.mm"
include "ex.mm"
include "finds.mm"

theorem ackbij2lem2
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
  assert |- ( A e. _om -> ( rec ( G , (/) ) ` A ) : ( R1 ` A ) -1-1-onto-> ( card ` ( R1 ` A ) ) )

  proof
    va
    cv
    #
    cr1
    cfv
    #
    @1
    ccrd
    cfv
    #
    @0
    cG
    c0
    crdg
    #
    cfv
    #
    wf1o
    c0
    cr1
    cfv
    #
    @5
    ccrd
    cfv
    #
    c0
    @3
    cfv
    #
    wf1o
    #
    vb
    cv
    #
    cr1
    cfv
    #
    @10
    ccrd
    cfv
    #
    @9
    @3
    cfv
    #
    wf1o
    #
    @9
    csuc
    #
    cr1
    cfv
    #
    @15
    ccrd
    cfv
    #
    @14
    @3
    cfv
    #
    wf1o
    #
    cA
    cr1
    cfv
    #
    @19
    ccrd
    cfv
    #
    cA
    @3
    cfv
    #
    wf1o
    va
    vb
    cA
    @0
    c0
    wceq
    #
    @1
    @5
    @2
    @6
    @4
    @7
    @0
    c0
    @3
    fveq2
    @0
    c0
    cr1
    fveq2
    #
    @22
    @1
    @5
    ccrd
    @23
    fveq2d
    f1oeq123d
    @0
    @9
    wceq
    #
    @1
    @10
    @2
    @11
    @4
    @12
    @0
    @9
    @3
    fveq2
    @0
    @9
    cr1
    fveq2
    #
    @24
    @1
    @10
    ccrd
    @25
    fveq2d
    f1oeq123d
    @0
    @14
    wceq
    #
    @1
    @15
    @2
    @16
    @4
    @17
    @0
    @14
    @3
    fveq2
    @0
    @14
    cr1
    fveq2
    #
    @26
    @1
    @15
    ccrd
    @27
    fveq2d
    f1oeq123d
    @0
    cA
    wceq
    #
    @1
    @19
    @2
    @20
    @4
    @21
    @0
    cA
    @3
    fveq2
    @0
    cA
    cr1
    fveq2
    #
    @28
    @1
    @19
    ccrd
    @29
    fveq2d
    f1oeq123d
    @8
    c0
    c0
    c0
    wf1o
    #
    f1o0
    @8
    @5
    @6
    c0
    wf1o
    #
    @30
    @7
    c0
    wceq
    @8
    @31
    wb
    c0
    cG
    0ex
    rdg0
    @5
    @6
    @7
    c0
    f1oeq1
    ax-mp
    @5
    c0
    wceq
    @6
    c0
    wceq
    @31
    @30
    wb
    r10
    @6
    c0
    ccrd
    cfv
    c0
    @5
    c0
    ccrd
    r10
    fveq2i
    card0
    eqtri
    @5
    c0
    @6
    c0
    c0
    f1oeq23
    mp2an
    bitri
    mpbir
    @9
    com
    wcel
    #
    @13
    @18
    @32
    @13
    wa
    #
    @18
    @10
    cpw
    #
    @34
    ccrd
    cfv
    #
    cF
    @11
    cpw
    #
    cres
    #
    va
    @34
    @12
    @0
    cima
    #
    cmpt
    #
    ccom
    #
    wf1o
    #
    @33
    @36
    @35
    @37
    wf1o
    #
    @34
    @36
    @39
    wf1o
    #
    @41
    @32
    @42
    @13
    @32
    @36
    cF
    @36
    cima
    #
    @37
    wf1o
    #
    @42
    @32
    com
    cpw
    cfn
    cin
    #
    com
    cF
    wf1
    #
    @36
    @46
    wss
    #
    @45
    @47
    @32
    vx
    vy
    cF
    ackbij.f
    ackbij1lem17
    a1i
    @32
    @11
    com
    wcel
    #
    @48
    @32
    @10
    cfn
    wcel
    #
    @49
    @9
    r1fin
    #
    @10
    ficardom
    syl
    #
    @11
    ackbij2lem1
    syl
    @46
    com
    @36
    cF
    f1ores
    syl2anc
    @32
    @44
    @35
    @36
    @37
    @32
    @44
    @36
    ccrd
    cfv
    #
    @35
    @32
    @49
    @44
    @53
    wceq
    @52
    vx
    vy
    @11
    cF
    ackbij.f
    ackbij1b
    syl
    @32
    @50
    @11
    @10
    cen
    wbr
    @36
    @34
    cen
    wbr
    @53
    @35
    wceq
    @51
    @10
    ficardid
    @11
    @10
    pwen
    @36
    @34
    carden2b
    4syl
    eqtrd
    f1oeq3d
    mpbid
    adantr
    @13
    @43
    @32
    @10
    @11
    @12
    va
    f1opw
    adantl
    #
    @34
    @36
    @35
    @37
    @39
    f1oco
    syl2anc
    #
    @33
    @18
    @15
    @16
    @40
    wf1o
    #
    @41
    @33
    @17
    @40
    wceq
    @18
    @56
    wb
    @33
    @17
    vy
    @12
    cdm
    #
    cpw
    #
    @12
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
    @40
    @32
    @17
    @62
    wceq
    @13
    @32
    @14
    @3
    com
    cres
    #
    cfv
    @9
    @63
    cfv
    #
    cG
    cfv
    #
    @17
    @62
    c0
    @9
    cG
    frsuc
    @32
    @14
    com
    @3
    @9
    peano2
    fvresd
    @32
    @65
    @12
    cG
    cfv
    #
    @62
    @32
    @64
    @12
    cG
    @9
    com
    @3
    fvres
    fveq2d
    @12
    cvv
    wcel
    @66
    @62
    wceq
    @9
    @3
    fvex
    #
    vx
    @12
    vy
    vx
    cv
    #
    cdm
    #
    cpw
    #
    @68
    @59
    cima
    #
    cF
    cfv
    #
    cmpt
    @62
    cvv
    cG
    @68
    @12
    wceq
    #
    vy
    @70
    @72
    @58
    @61
    @73
    @69
    @57
    @68
    @12
    dmeq
    pweqd
    @73
    @71
    @60
    cF
    @68
    @12
    @59
    imaeq1
    fveq2d
    mpteq12dv
    ackbij.g
    vy
    @58
    @61
    @57
    @12
    @67
    dmex
    pwex
    mptex
    fvmpt
    ax-mp
    syl6eq
    3eqtr3d
    adantr
    @33
    @62
    vy
    @34
    @61
    cmpt
    #
    @40
    @33
    vy
    @58
    @34
    @61
    @33
    @57
    @10
    @13
    @57
    @10
    wceq
    @32
    @10
    @11
    @12
    f1odm
    adantl
    pweqd
    mpteq1d
    @33
    vc
    @34
    @74
    @40
    @74
    @34
    wfn
    @33
    vy
    @34
    @61
    @74
    @60
    cF
    fvex
    @74
    eqid
    #
    fnmpti
    a1i
    @33
    @41
    @40
    @34
    wfn
    @55
    @34
    @35
    @40
    f1ofn
    syl
    @33
    vc
    cv
    #
    @34
    wcel
    #
    wa
    #
    @76
    @39
    cfv
    #
    @37
    cfv
    #
    @12
    @76
    cima
    #
    cF
    cfv
    #
    @76
    @40
    cfv
    #
    @76
    @74
    cfv
    #
    @78
    @80
    @79
    cF
    cfv
    @82
    @78
    @79
    @36
    cF
    @33
    @34
    @36
    @76
    @39
    @33
    @43
    @34
    @36
    @39
    wf
    #
    @54
    @34
    @36
    @39
    f1of
    syl
    #
    ffvelrnda
    fvresd
    @78
    @79
    @81
    cF
    @77
    @79
    @81
    wceq
    @33
    va
    @76
    @38
    @81
    @34
    @39
    @0
    @76
    @12
    imaeq2
    @39
    eqid
    @12
    @76
    @67
    imaex
    fvmpt
    adantl
    fveq2d
    eqtrd
    @33
    @85
    @77
    @83
    @80
    wceq
    @86
    @34
    @36
    @76
    @37
    @39
    fvco3
    sylan
    @77
    @84
    @82
    wceq
    @33
    vy
    @76
    @61
    @82
    @34
    @74
    @59
    @76
    wceq
    @60
    @81
    cF
    @59
    @76
    @12
    imaeq2
    fveq2d
    @75
    @81
    cF
    fvex
    fvmpt
    adantl
    3eqtr4rd
    eqfnfvd
    eqtrd
    eqtrd
    @15
    @16
    @17
    @40
    f1oeq1
    syl
    @32
    @56
    @41
    wb
    #
    @13
    @32
    @15
    @34
    wceq
    #
    @16
    @35
    wceq
    @87
    @32
    @9
    con0
    wcel
    @88
    @9
    nnon
    @9
    r1suc
    syl
    #
    @32
    @15
    @34
    ccrd
    @89
    fveq2d
    @15
    @34
    @16
    @35
    @40
    f1oeq23
    syl2anc
    adantr
    bitrd
    mpbird
    ex
    finds
end
