include "cfv.mm"
include "cres.mm"
include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "cr1.mm"
include "cuni.mm"
include "wceq.mm"
include "crn.mm"
include "csuc.mm"
include "crnk.mm"
include "comu.mm"
include "co.mm"
include "coa.mm"
include "cep.mm"
include "coi.mm"
include "ccnv.mm"
include "ccom.mm"
include "cima.mm"
include "cif.mm"
include "cmpt.mm"
include "con0.mm"
include "wcel.mm"
include "tfr2.mm"
include "syl.mm"
include "wfun.mm"
include "wfn.mm"
include "tfr1.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "resfunexg.mm"
include "sylancr.mm"
include "dmeq.mm"
include "fveq2d.mm"
include "unieqd.mm"
include "eqeq12d.mm"
include "rneq.mm"
include "df-ima.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "suceq.mm"
include "oveq1d.mm"
include "fveq1.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "id.mm"
include "fveq12d.mm"
include "oieq2.mm"
include "cnveqd.mm"
include "coeq12d.mm"
include "imaeq1d.mm"
include "ifbieq12d.mm"
include "mpteq12dv.mm"
include "eqid.mm"
include "fvex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "wss.mm"
include "onss.mm"
include "fnssres.mm"
include "fndm.mm"
include "mpteq1d.mm"
include "wa.mm"
include "adantr.mm"
include "ifbid.mm"
include "rankr1ai.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "wb.mm"
include "word.mm"
include "eloni.mm"
include "ordsucuniel.mm"
include "3syl.mm"
include "ad2antrr.mm"
include "mpbid.mm"
include "fvres.mm"
include "oveq2d.mm"
include "ifeq1da.mm"
include "wn.mm"
include "uniexg.mm"
include "sucidg.mm"
include "wo.mm"
include "orduniorsuc.mm"
include "orcanai.mm"
include "eleqtrrd.mm"
include "eqtrd.mm"
include "ifeq2da.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"

theorem dfac12lem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cF: class F
  let cG: class G
  let cH: class H
  let vm: setvar m
  let vn: setvar n
  let vz: setvar z
  assume dfac12.1: |- ( ph -> A e. On )
  assume dfac12.3: |- ( ph -> F : ~P ( har ` ( R1 ` A ) ) -1-1-> On )
  assume dfac12.4: |- G = recs ( ( x e. _V |-> ( y e. ( R1 ` dom x ) |-> if ( dom x = U. dom x , ( ( suc U. ran U. ran x .o ( rank ` y ) ) +o ( ( x ` suc ( rank ` y ) ) ` y ) ) , ( F ` ( ( `' OrdIso ( _E , ran ( x ` U. dom x ) ) o. ( x ` U. dom x ) ) " y ) ) ) ) ) )
  assume dfac12.5: |- ( ph -> C e. On )
  assume dfac12.h: |- H = ( `' OrdIso ( _E , ran ( G ` U. C ) ) o. ( G ` U. C ) )

  disjoint A y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint G x
  disjoint G y
  disjoint ph y
  disjoint F x
  disjoint F y
  disjoint H y
  disjoint m n
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint y z
  disjoint A z
  disjoint x z
  disjoint C z
  disjoint m x
  disjoint G m
  disjoint n x
  disjoint G n
  disjoint G z
  disjoint m ph
  disjoint n ph
  disjoint ph z
  disjoint F z
  disjoint H z
  assert |- ( ph -> ( G ` C ) = ( y e. ( R1 ` C ) |-> if ( C = U. C , ( ( suc U. ran U. ( G " C ) .o ( rank ` y ) ) +o ( ( G ` suc ( rank ` y ) ) ` y ) ) , ( F ` ( H " y ) ) ) ) )

  proof
    wph
    cC
    cG
    cfv
    #
    cG
    cC
    cres
    #
    vx
    cvv
    vy
    vx
    cv
    #
    cdm
    #
    cr1
    cfv
    #
    @3
    @3
    cuni
    #
    wceq
    #
    @2
    crn
    #
    cuni
    #
    crn
    #
    cuni
    #
    csuc
    #
    vy
    cv
    #
    crnk
    cfv
    #
    comu
    co
    #
    @12
    @13
    csuc
    #
    @2
    cfv
    #
    cfv
    #
    coa
    co
    #
    @5
    @2
    cfv
    #
    crn
    #
    cep
    coi
    #
    ccnv
    #
    @19
    ccom
    #
    @12
    cima
    #
    cF
    cfv
    #
    cif
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    vy
    @1
    cdm
    #
    cr1
    cfv
    #
    @30
    @30
    cuni
    #
    wceq
    #
    cG
    cC
    cima
    #
    cuni
    #
    crn
    #
    cuni
    #
    csuc
    #
    @13
    comu
    co
    #
    @12
    @15
    @1
    cfv
    #
    cfv
    #
    coa
    co
    #
    @32
    @1
    cfv
    #
    crn
    #
    cep
    coi
    #
    ccnv
    #
    @43
    ccom
    #
    @12
    cima
    #
    cF
    cfv
    #
    cif
    #
    cmpt
    #
    vy
    cC
    cr1
    cfv
    #
    cC
    cC
    cuni
    #
    wceq
    #
    @39
    @12
    @15
    cG
    cfv
    #
    cfv
    #
    coa
    co
    #
    cH
    @12
    cima
    #
    cF
    cfv
    #
    cif
    #
    cmpt
    #
    wph
    cC
    con0
    wcel
    #
    @0
    @29
    wceq
    dfac12.5
    cC
    cG
    @28
    dfac12.4
    tfr2
    syl
    wph
    @1
    cvv
    wcel
    #
    @29
    @51
    wceq
    wph
    cG
    wfun
    #
    @62
    @63
    cG
    con0
    wfn
    #
    @64
    cG
    @28
    dfac12.4
    tfr1
    #
    con0
    cG
    fnfun
    ax-mp
    dfac12.5
    cG
    cC
    con0
    resfunexg
    sylancr
    vx
    @1
    @27
    @51
    cvv
    @28
    @2
    @1
    wceq
    #
    vy
    @4
    @26
    @31
    @50
    @67
    @3
    @30
    cr1
    @2
    @1
    dmeq
    #
    fveq2d
    @67
    @6
    @33
    @18
    @25
    @42
    @49
    @67
    @3
    @30
    @5
    @32
    @68
    @67
    @3
    @30
    @68
    unieqd
    #
    eqeq12d
    @67
    @14
    @39
    @17
    @41
    coa
    @67
    @11
    @38
    @13
    comu
    @67
    @10
    @37
    wceq
    @11
    @38
    wceq
    @67
    @9
    @36
    @67
    @8
    @35
    @67
    @7
    @34
    @67
    @7
    @1
    crn
    @34
    @2
    @1
    rneq
    cG
    cC
    df-ima
    syl6eqr
    unieqd
    rneqd
    unieqd
    @10
    @37
    suceq
    syl
    oveq1d
    @67
    @12
    @16
    @40
    @15
    @2
    @1
    fveq1
    fveq1d
    oveq12d
    @67
    @24
    @48
    cF
    @67
    @23
    @47
    @12
    @67
    @22
    @46
    @19
    @43
    @67
    @21
    @45
    @67
    @20
    @44
    wceq
    @21
    @45
    wceq
    @67
    @19
    @43
    @67
    @5
    @32
    @2
    @1
    @67
    id
    @69
    fveq12d
    #
    rneqd
    @20
    @44
    cep
    oieq2
    syl
    cnveqd
    @70
    coeq12d
    imaeq1d
    fveq2d
    ifbieq12d
    mpteq12dv
    @28
    eqid
    vy
    @31
    @50
    @30
    cr1
    fvex
    mptex
    fvmpt
    syl
    wph
    @51
    vy
    @52
    @50
    cmpt
    @61
    wph
    vy
    @31
    @52
    @50
    wph
    @30
    cC
    cr1
    wph
    @1
    cC
    wfn
    #
    @30
    cC
    wceq
    #
    wph
    @65
    cC
    con0
    wss
    #
    @71
    @66
    wph
    @62
    @73
    dfac12.5
    cC
    onss
    syl
    con0
    cC
    cG
    fnssres
    sylancr
    cC
    @1
    fndm
    syl
    #
    fveq2d
    mpteq1d
    wph
    vy
    @52
    @50
    @60
    wph
    @12
    @52
    wcel
    #
    wa
    #
    @50
    @54
    @42
    @49
    cif
    @54
    @57
    @49
    cif
    @60
    @76
    @33
    @54
    @42
    @49
    @76
    @30
    cC
    @32
    @53
    wph
    @72
    @75
    @74
    adantr
    #
    @76
    @30
    cC
    @77
    unieqd
    #
    eqeq12d
    ifbid
    @76
    @54
    @42
    @57
    @49
    @76
    @54
    wa
    #
    @41
    @56
    @39
    coa
    @79
    @12
    @40
    @55
    @79
    @15
    cC
    wcel
    #
    @40
    @55
    wceq
    @79
    @13
    @53
    wcel
    #
    @80
    @79
    @13
    cC
    @53
    @75
    @13
    cC
    wcel
    wph
    @54
    @12
    cC
    rankr1ai
    ad2antlr
    @76
    @54
    simpr
    eleqtrd
    wph
    @81
    @80
    wb
    #
    @75
    @54
    wph
    @62
    cC
    word
    #
    @82
    dfac12.5
    cC
    eloni
    #
    @13
    cC
    ordsucuniel
    3syl
    ad2antrr
    mpbid
    @15
    cC
    cG
    fvres
    syl
    fveq1d
    oveq2d
    ifeq1da
    @76
    @54
    @49
    @59
    @57
    @76
    @54
    wn
    #
    wa
    #
    @48
    @58
    cF
    @86
    @47
    cH
    @12
    @86
    @47
    @53
    cG
    cfv
    #
    crn
    #
    cep
    coi
    #
    ccnv
    #
    @87
    ccom
    cH
    @86
    @46
    @90
    @43
    @87
    @86
    @45
    @89
    @86
    @44
    @88
    wceq
    @45
    @89
    wceq
    @86
    @43
    @87
    @86
    @43
    @53
    @1
    cfv
    #
    @87
    @86
    @32
    @53
    @1
    @76
    @32
    @53
    wceq
    @85
    @78
    adantr
    fveq2d
    @86
    @53
    cC
    wcel
    @91
    @87
    wceq
    @86
    @53
    @53
    csuc
    #
    cC
    @86
    @62
    @53
    cvv
    wcel
    @53
    @92
    wcel
    wph
    @62
    @75
    @85
    dfac12.5
    ad2antrr
    cC
    con0
    uniexg
    @53
    cvv
    sucidg
    3syl
    @76
    @54
    cC
    @92
    wceq
    #
    @76
    @62
    @83
    @54
    @93
    wo
    wph
    @62
    @75
    dfac12.5
    adantr
    @84
    cC
    orduniorsuc
    3syl
    orcanai
    eleqtrrd
    @53
    cC
    cG
    fvres
    syl
    eqtrd
    #
    rneqd
    @44
    @88
    cep
    oieq2
    syl
    cnveqd
    @94
    coeq12d
    dfac12.h
    syl6eqr
    imaeq1d
    fveq2d
    ifeq2da
    3eqtrd
    mpteq2dva
    eqtrd
    3eqtrd
end
