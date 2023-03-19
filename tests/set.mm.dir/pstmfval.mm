include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cec.mm"
include "cpstm.mm"
include "co.mm"
include "cqs.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "cmpt2.mm"
include "pstmval.mm"
include "3ad2ant1.mm"
include "oveqd.mm"
include "cmetid.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ecelqsi.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "rexeq.mm"
include "abbidv.mm"
include "unieqd.mm"
include "rexbidv.mm"
include "eqid.mm"
include "ecexg.mm"
include "ax-mp.mm"
include "ab2rexex.mm"
include "uniex.mm"
include "ovmpt2.mm"
include "syl2anc.mm"
include "csn.mm"
include "wa.mm"
include "simpr3.mm"
include "wbr.mm"
include "simpl1.mm"
include "simpr1.mm"
include "wrel.mm"
include "wb.mm"
include "cxp.mm"
include "wss.mm"
include "metidss.mm"
include "syl5eqss.mm"
include "xpss.mm"
include "syl6ss.mm"
include "df-rel.mm"
include "sylibr.mm"
include "adantr.mm"
include "relelec.mm"
include "syl.mm"
include "mpbid.mm"
include "breqi.mm"
include "sylib.mm"
include "simpr2.mm"
include "metideq.mm"
include "syl12anc.mm"
include "eqtr4d.mm"
include "adantlr.mm"
include "3anassrs.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "oveq2.mm"
include "cbvrex2v.mm"
include "biimpi.mm"
include "adantl.mm"
include "r19.29vva.mm"
include "cc0.mm"
include "simpl2.mm"
include "psmet0.mm"
include "3syl.mm"
include "a1i.mm"
include "breqd.mm"
include "metidv.mm"
include "3bitrd.mm"
include "mpbird.mm"
include "simpl3.mm"
include "simpr.mm"
include "rspceov.mm"
include "syl3anc.mm"
include "impbida.mm"
include "df-sn.mm"
include "syl6eqr.mm"
include "ovex.mm"
include "unisn.mm"
include "syl6eq.mm"
include "3eqtrd.mm"

theorem pstmfval
  let cA: class A
  let cB: class B
  let cD: class D
  let c.sm: class .~
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let ve: setvar e
  let vf: setvar f
  assume pstmval.1: |- .~ = ( ~Met ` D )


  assert |- ( ( D e. ( PsMet ` X ) /\ A e. X /\ B e. X ) -> ( [ A ] .~ ( pstoMet ` D ) [ B ] .~ ) = ( A D B ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    c.sm
    cec
    #
    cB
    c.sm
    cec
    #
    cD
    cpstm
    cfv
    #
    co
    @4
    @5
    vx
    vy
    cX
    c.sm
    cqs
    #
    @7
    vz
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    cD
    co
    #
    wceq
    #
    vb
    vy
    cv
    #
    wrex
    #
    va
    vx
    cv
    #
    wrex
    #
    vz
    cab
    #
    cuni
    #
    cmpt2
    #
    co
    #
    @12
    vb
    @5
    wrex
    #
    va
    @4
    wrex
    #
    vz
    cab
    #
    cuni
    #
    cA
    cB
    cD
    co
    #
    @3
    @6
    @19
    @4
    @5
    @0
    @1
    @6
    @19
    wceq
    @2
    va
    vb
    vz
    cD
    c.sm
    cX
    vx
    vy
    pstmval.1
    pstmval
    3ad2ant1
    oveqd
    @3
    @4
    @7
    wcel
    #
    @5
    @7
    wcel
    #
    @20
    @24
    wceq
    @1
    @0
    @26
    @2
    cX
    cA
    c.sm
    c.sm
    cD
    cmetid
    cfv
    #
    cvv
    pstmval.1
    cD
    cmetid
    fvex
    eqeltri
    #
    ecelqsi
    3ad2ant2
    @2
    @0
    @27
    @1
    cX
    cB
    c.sm
    @29
    ecelqsi
    3ad2ant3
    vx
    vy
    @4
    @5
    @7
    @7
    @18
    @24
    @19
    @14
    va
    @4
    wrex
    #
    vz
    cab
    #
    cuni
    @15
    @4
    wceq
    #
    @17
    @31
    @32
    @16
    @30
    vz
    @14
    va
    @15
    @4
    rexeq
    abbidv
    unieqd
    @13
    @5
    wceq
    #
    @31
    @23
    @33
    @30
    @22
    vz
    @33
    @14
    @21
    va
    @4
    @12
    vb
    @13
    @5
    rexeq
    rexbidv
    abbidv
    unieqd
    @19
    eqid
    @23
    va
    vb
    vz
    @4
    @5
    @11
    c.sm
    cvv
    wcel
    #
    @4
    cvv
    wcel
    @29
    cA
    cvv
    c.sm
    ecexg
    ax-mp
    @34
    @5
    cvv
    wcel
    @29
    cB
    cvv
    c.sm
    ecexg
    ax-mp
    ab2rexex
    uniex
    ovmpt2
    syl2anc
    @3
    @24
    @25
    csn
    #
    cuni
    @25
    @3
    @23
    @35
    @3
    @23
    @8
    @25
    wceq
    #
    vz
    cab
    @35
    @3
    @22
    @36
    vz
    @3
    @22
    @36
    @3
    @22
    wa
    #
    @8
    ve
    cv
    #
    vf
    cv
    #
    cD
    co
    #
    wceq
    #
    @36
    ve
    vf
    @4
    @5
    @37
    @38
    @4
    wcel
    #
    @39
    @5
    wcel
    #
    @41
    @36
    @3
    @42
    @43
    @41
    w3a
    #
    @36
    @22
    @3
    @44
    wa
    #
    @8
    @40
    @25
    @3
    @42
    @43
    @41
    simpr3
    @45
    @0
    cA
    @38
    @28
    wbr
    #
    cB
    @39
    @28
    wbr
    #
    @25
    @40
    wceq
    @0
    @1
    @2
    @44
    simpl1
    @45
    cA
    @38
    c.sm
    wbr
    #
    @46
    @45
    @42
    @48
    @3
    @42
    @43
    @41
    simpr1
    @45
    c.sm
    wrel
    #
    @42
    @48
    wb
    @3
    @49
    @44
    @0
    @1
    @49
    @2
    @0
    c.sm
    cvv
    cvv
    cxp
    #
    wss
    @49
    @0
    c.sm
    cX
    cX
    cxp
    #
    @50
    @0
    c.sm
    @28
    @51
    pstmval.1
    cD
    cX
    metidss
    syl5eqss
    cX
    cX
    xpss
    syl6ss
    c.sm
    df-rel
    sylibr
    #
    3ad2ant1
    adantr
    #
    @38
    cA
    c.sm
    relelec
    syl
    mpbid
    cA
    @38
    c.sm
    @28
    pstmval.1
    breqi
    sylib
    @45
    cB
    @39
    c.sm
    wbr
    #
    @47
    @45
    @43
    @54
    @3
    @42
    @43
    @41
    simpr2
    @45
    @49
    @43
    @54
    wb
    @53
    @39
    cB
    c.sm
    relelec
    syl
    mpbid
    cB
    @39
    c.sm
    @28
    pstmval.1
    breqi
    sylib
    cA
    @38
    cD
    cB
    @39
    cX
    metideq
    syl12anc
    eqtr4d
    adantlr
    3anassrs
    @22
    @41
    vf
    @5
    wrex
    ve
    @4
    wrex
    #
    @3
    @22
    @55
    @12
    @41
    @8
    @38
    @10
    cD
    co
    #
    wceq
    va
    vb
    ve
    vf
    @4
    @5
    @9
    @38
    wceq
    @11
    @56
    @8
    @9
    @38
    @10
    cD
    oveq1
    eqeq2d
    @10
    @39
    wceq
    @56
    @40
    @8
    @10
    @39
    @38
    cD
    oveq2
    eqeq2d
    cbvrex2v
    biimpi
    adantl
    r19.29vva
    @3
    @36
    wa
    #
    cA
    @4
    wcel
    #
    cB
    @5
    wcel
    #
    @36
    @22
    @57
    @58
    cA
    cA
    cD
    co
    cc0
    wceq
    #
    @57
    @0
    @1
    @60
    @0
    @1
    @2
    @36
    simpl1
    #
    @0
    @1
    @2
    @36
    simpl2
    #
    cA
    cD
    cX
    psmet0
    syl2anc
    @57
    @58
    cA
    cA
    c.sm
    wbr
    #
    cA
    cA
    @28
    wbr
    #
    @60
    @57
    @0
    @49
    @58
    @63
    wb
    @61
    @52
    cA
    cA
    c.sm
    relelec
    3syl
    @57
    c.sm
    @28
    cA
    cA
    c.sm
    @28
    wceq
    @57
    pstmval.1
    a1i
    #
    breqd
    @57
    @0
    @1
    @1
    @64
    @60
    wb
    @61
    @62
    @62
    cA
    cA
    cD
    cX
    metidv
    syl12anc
    3bitrd
    mpbird
    @57
    @59
    cB
    cB
    cD
    co
    cc0
    wceq
    #
    @57
    @0
    @2
    @66
    @61
    @0
    @1
    @2
    @36
    simpl3
    #
    cB
    cD
    cX
    psmet0
    syl2anc
    @57
    @59
    cB
    cB
    c.sm
    wbr
    #
    cB
    cB
    @28
    wbr
    #
    @66
    @57
    @0
    @49
    @59
    @68
    wb
    @61
    @52
    cB
    cB
    c.sm
    relelec
    3syl
    @57
    c.sm
    @28
    cB
    cB
    @65
    breqd
    @57
    @0
    @2
    @2
    @69
    @66
    wb
    @61
    @67
    @67
    cB
    cB
    cD
    cX
    metidv
    syl12anc
    3bitrd
    mpbird
    @3
    @36
    simpr
    va
    vb
    @4
    @5
    cA
    cB
    @8
    cD
    rspceov
    syl3anc
    impbida
    abbidv
    vz
    @25
    df-sn
    syl6eqr
    unieqd
    @25
    cA
    cB
    cD
    ovex
    unisn
    syl6eq
    3eqtrd
end
