include "ccrg.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "csymg.mm"
include "cbs.mm"
include "cv.mm"
include "czrh.mm"
include "cpsgn.mm"
include "ccom.mm"
include "cmgp.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmulr.mm"
include "cop.mm"
include "eqid.mm"
include "mdetleib.mm"
include "3ad2ant3.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "adantr.mm"
include "3ad2ant2.mm"
include "simp2r.mm"
include "symg1bas.mm"
include "syl.mm"
include "eqtrd.mm"
include "mpteq1d.mm"
include "cvv.mm"
include "snex.mm"
include "a1i.mm"
include "ovex.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "fmptsng.mm"
include "eqcomd.mm"
include "sylancl.mm"
include "cur.mm"
include "c1.mm"
include "wfn.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cfn.mm"
include "crab.mm"
include "psgnfn.mm"
include "c0.mm"
include "cif.mm"
include "adantl.mm"
include "rabeq.mm"
include "difeq1.mm"
include "dmeqd.mm"
include "eleq1d.mm"
include "rabsnif.mm"
include "cres.mm"
include "cxp.mm"
include "restidsing.mm"
include "xpsng.mm"
include "anidms.mm"
include "syl5req.mm"
include "wb.mm"
include "fnsng.mm"
include "fnnfpeq0.mm"
include "mpbird.mm"
include "0fin.mm"
include "syl6eqel.mm"
include "iftrued.mm"
include "3eqtrrd.mm"
include "fneq2d.mm"
include "mpbiri.mm"
include "snid.mm"
include "fvco2.mm"
include "fveq1d.mm"
include "snidg.mm"
include "mp1i.mm"
include "eleqtrrd.mm"
include "ancli.mm"
include "psgnsn.mm"
include "crg.mm"
include "crngring.mm"
include "3ad2ant1.mm"
include "zrh1.mm"
include "3eqtrd.mm"
include "simp2l.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "eleq2.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "simpl.mm"
include "simpr.mm"
include "3jca.mm"
include "syl2an.mm"
include "3adant1.mm"
include "matecl.mm"
include "mgpbas.mm"
include "syl6eleq.mm"
include "eqvisset.mm"
include "fvsng.mm"
include "syl2anc.mm"
include "id.mm"
include "gsumsn.mm"
include "syl3anc.mm"
include "ringlidm.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "eqidd.mm"
include "ringmnd.mm"

theorem m1detdiag
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cI: class I
  let cM: class M
  let cN: class N
  let cV: class V
  let vb: setvar b
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  assume mdetdiag.d: |- D = ( N maDet R )
  assume mdetdiag.a: |- A = ( N Mat R )
  assume mdetdiag.b: |- B = ( Base ` A )


  assert |- ( ( R e. CRing /\ ( N = { I } /\ I e. V ) /\ M e. B ) -> ( D ` M ) = ( I M I ) )

  proof
    cR
    ccrg
    wcel
    #
    cN
    cI
    csn
    #
    wceq
    #
    cI
    cV
    wcel
    #
    wa
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cM
    cD
    cfv
    #
    cR
    vp
    cN
    csymg
    cfv
    #
    cbs
    cfv
    #
    vp
    cv
    #
    cR
    czrh
    cfv
    #
    cN
    cpsgn
    cfv
    #
    ccom
    #
    cfv
    #
    cR
    cmgp
    cfv
    #
    vx
    cN
    vx
    cv
    #
    @10
    cfv
    #
    @16
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    vy
    cI
    cI
    cop
    #
    csn
    #
    csn
    #
    cI
    cI
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @28
    @5
    @0
    @7
    @24
    wceq
    @4
    vx
    cA
    cB
    cD
    @9
    cR
    @12
    @21
    @15
    cM
    cN
    @11
    vp
    mdetdiag.d
    mdetdiag.a
    mdetdiag.b
    @9
    eqid
    #
    @11
    eqid
    #
    @12
    eqid
    #
    @21
    eqid
    #
    @15
    eqid
    #
    mdetleib
    3ad2ant3
    @6
    @23
    @29
    cR
    cgsu
    @6
    @23
    vp
    @27
    @22
    cmpt
    #
    @26
    @26
    @13
    cfv
    #
    @15
    vx
    cN
    @16
    @26
    cfv
    #
    @16
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @21
    co
    #
    cop
    #
    csn
    #
    @29
    @6
    vp
    @9
    @27
    @22
    @6
    @9
    @1
    csymg
    cfv
    #
    cbs
    cfv
    #
    @27
    @4
    @0
    @9
    @46
    wceq
    #
    @5
    @2
    @47
    @3
    @2
    @8
    @45
    cbs
    cN
    @1
    csymg
    fveq2
    fveq2d
    adantr
    #
    3ad2ant2
    @6
    @3
    @46
    @27
    wceq
    #
    @0
    @2
    @3
    @5
    simp2r
    #
    @1
    @46
    @45
    cI
    cV
    @45
    eqid
    #
    @46
    eqid
    #
    @1
    eqid
    #
    symg1bas
    #
    syl
    eqtrd
    mpteq1d
    @6
    @26
    cvv
    wcel
    #
    @42
    cvv
    wcel
    #
    @36
    @44
    wceq
    @55
    @6
    @25
    snex
    #
    a1i
    #
    @37
    @41
    @21
    ovex
    @55
    @56
    wa
    @44
    @36
    vp
    @26
    @22
    @42
    cvv
    cvv
    @10
    @26
    wceq
    #
    @14
    @37
    @20
    @41
    @21
    @10
    @26
    @13
    fveq2
    @59
    @19
    @40
    @15
    cgsu
    @59
    vx
    cN
    @18
    @39
    @59
    @17
    @38
    @16
    cM
    @16
    @10
    @26
    fveq1
    oveq1d
    mpteq2dv
    oveq2d
    oveq12d
    fmptsng
    eqcomd
    sylancl
    @6
    @44
    @26
    @28
    cop
    #
    csn
    #
    @29
    @6
    @43
    @60
    @6
    @42
    @28
    @26
    @6
    @42
    cR
    cur
    cfv
    #
    @28
    @21
    co
    #
    @28
    @6
    @37
    @62
    @41
    @28
    @21
    @6
    @37
    @26
    @12
    cfv
    #
    @11
    cfv
    #
    c1
    @11
    cfv
    #
    @62
    @6
    @12
    @27
    wfn
    #
    @26
    @27
    wcel
    #
    @37
    @65
    wceq
    @6
    @67
    @12
    vb
    cv
    #
    cid
    cdif
    #
    cdm
    #
    cfn
    wcel
    #
    vb
    @9
    crab
    #
    wfn
    @9
    cN
    @73
    @8
    @12
    vb
    @8
    eqid
    @31
    @73
    eqid
    @33
    psgnfn
    @6
    @27
    @73
    @12
    @6
    @73
    @72
    vb
    @27
    crab
    #
    @26
    cid
    cdif
    #
    cdm
    #
    cfn
    wcel
    #
    @27
    c0
    cif
    #
    @27
    @6
    @9
    @27
    wceq
    #
    @73
    @74
    wceq
    @4
    @0
    @79
    @5
    @4
    @9
    @46
    @27
    @48
    @3
    @49
    @2
    @54
    adantl
    eqtrd
    3ad2ant2
    @72
    vb
    @9
    @27
    rabeq
    syl
    @74
    @78
    wceq
    @6
    @72
    @77
    vb
    @26
    @69
    @26
    wceq
    #
    @71
    @76
    cfn
    @80
    @70
    @75
    @69
    @26
    cid
    difeq1
    dmeqd
    eleq1d
    rabsnif
    a1i
    @6
    @77
    @27
    c0
    @4
    @0
    @77
    @5
    @3
    @77
    @2
    @3
    @76
    c0
    cfn
    @3
    @76
    c0
    wceq
    #
    @26
    cid
    @1
    cres
    #
    wceq
    #
    @3
    @82
    @1
    @1
    cxp
    #
    @26
    cI
    restidsing
    @3
    @84
    @26
    wceq
    cI
    cI
    cV
    cV
    xpsng
    anidms
    syl5req
    @3
    @26
    @1
    wfn
    #
    @81
    @83
    wb
    @3
    @85
    cI
    cI
    cV
    cV
    fnsng
    anidms
    @1
    @26
    fnnfpeq0
    syl
    mpbird
    0fin
    syl6eqel
    adantl
    3ad2ant2
    iftrued
    3eqtrrd
    fneq2d
    mpbiri
    @26
    @57
    snid
    @27
    @11
    @12
    @26
    fvco2
    sylancl
    @6
    @64
    c1
    @11
    @6
    @64
    @26
    @1
    cpsgn
    cfv
    #
    cfv
    #
    c1
    @6
    @26
    @12
    @86
    @4
    @0
    @12
    @86
    wceq
    #
    @5
    @2
    @88
    @3
    cN
    @1
    cpsgn
    fveq2
    adantr
    3ad2ant2
    fveq1d
    @6
    @3
    @26
    @46
    wcel
    #
    wa
    #
    @87
    c1
    wceq
    @4
    @0
    @90
    @5
    @3
    @90
    @2
    @3
    @89
    @3
    @26
    @27
    @46
    @55
    @68
    @3
    @57
    @26
    cvv
    snidg
    mp1i
    @54
    eleqtrrd
    ancli
    adantl
    3ad2ant2
    cI
    @46
    @1
    @45
    @86
    cV
    @26
    @53
    @51
    @52
    @86
    eqid
    psgnsn
    syl
    eqtrd
    fveq2d
    @6
    cR
    crg
    wcel
    #
    @66
    @62
    wceq
    @0
    @4
    @91
    @5
    cR
    crngring
    #
    3ad2ant1
    #
    cR
    @62
    @11
    @32
    @62
    eqid
    #
    zrh1
    syl
    3eqtrd
    @6
    @41
    @15
    vx
    @1
    @39
    cmpt
    #
    cgsu
    co
    #
    @28
    @6
    @40
    @95
    @15
    cgsu
    @6
    vx
    cN
    @1
    @39
    @0
    @2
    @3
    @5
    simp2l
    mpteq1d
    oveq2d
    @6
    @15
    cmnd
    wcel
    #
    @3
    @28
    @15
    cbs
    cfv
    #
    wcel
    @96
    @28
    wceq
    @0
    @4
    @97
    @5
    @0
    @91
    @97
    @92
    cR
    @15
    @35
    ringmgp
    syl
    3ad2ant1
    @50
    @6
    @28
    cR
    cbs
    cfv
    #
    @98
    @6
    cI
    cN
    wcel
    #
    @100
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    w3a
    #
    @28
    @99
    wcel
    #
    @4
    @5
    @103
    @0
    @4
    @100
    @102
    @103
    @5
    @4
    @100
    cI
    @1
    wcel
    #
    @3
    @105
    @2
    cI
    cV
    snidg
    adantl
    @2
    @100
    @105
    wb
    @3
    cN
    @1
    cI
    eleq2
    adantr
    mpbird
    #
    @5
    @102
    cB
    @101
    cM
    mdetdiag.b
    eleq2i
    biimpi
    #
    @100
    @102
    wa
    @100
    @100
    @102
    @100
    @102
    simpl
    #
    @108
    @100
    @102
    simpr
    3jca
    syl2an
    3adant1
    cA
    cR
    cI
    cI
    @99
    cM
    cN
    mdetdiag.a
    @99
    eqid
    #
    matecl
    #
    syl
    @99
    cR
    @15
    @35
    @109
    mgpbas
    syl6eleq
    @39
    @98
    @28
    vx
    @15
    cI
    cV
    @98
    eqid
    @16
    cI
    wceq
    #
    @38
    cI
    @16
    cI
    cM
    @111
    @38
    cI
    @26
    cfv
    #
    cI
    @16
    cI
    @26
    fveq2
    @111
    cI
    cvv
    wcel
    #
    @113
    @112
    cI
    wceq
    vx
    cI
    eqvisset
    #
    @114
    cI
    cI
    cvv
    cvv
    fvsng
    syl2anc
    eqtrd
    @111
    id
    oveq12d
    gsumsn
    syl3anc
    eqtrd
    oveq12d
    @6
    @91
    @104
    @63
    @28
    wceq
    @93
    @6
    @100
    @100
    @102
    @104
    @4
    @0
    @100
    @5
    @106
    3ad2ant2
    #
    @115
    @5
    @0
    @102
    @4
    @107
    3ad2ant3
    @110
    syl3anc
    #
    @99
    cR
    @21
    @62
    @28
    @109
    @34
    @94
    ringlidm
    syl2anc
    eqtrd
    opeq2d
    sneqd
    @6
    @55
    @28
    cvv
    wcel
    @61
    @29
    wceq
    @58
    cI
    cI
    cM
    ovex
    vy
    @26
    @28
    @28
    cvv
    cvv
    vy
    cv
    @26
    wceq
    @28
    eqidd
    #
    fmptsng
    sylancl
    eqtrd
    3eqtrd
    oveq2d
    @6
    cR
    cmnd
    wcel
    #
    @55
    @104
    @30
    @28
    wceq
    @0
    @4
    @118
    @5
    @0
    @91
    @118
    @92
    cR
    ringmnd
    syl
    3ad2ant1
    @58
    @116
    @28
    @99
    @28
    vy
    cR
    @26
    cvv
    @109
    @117
    gsumsn
    syl3anc
    3eqtrd
end
