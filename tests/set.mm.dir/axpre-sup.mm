include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cltrr.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "cltr.mm"
include "c1st.mm"
include "cima.mm"
include "cnr.mm"
include "wcel.mm"
include "cfv.mm"
include "c0r.mm"
include "cop.mm"
include "wceq.mm"
include "elreal2.mm"
include "simplbi.mm"
include "adantl.mm"
include "cvv.mm"
include "wfn.mm"
include "wb.mm"
include "wfo.mm"
include "wf.mm"
include "fo1st.mm"
include "fof.mm"
include "ffn.mm"
include "mp2b.mm"
include "ssv.mm"
include "fvelimab.mm"
include "mp2an.mm"
include "r19.29.mm"
include "ssel2.mm"
include "ltresr2.mm"
include "breq1.mm"
include "sylan9bb.mm"
include "biimpd.mm"
include "exp31.mm"
include "syl.mm"
include "imp4b.mm"
include "ancomsd.mm"
include "an32s.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "expd.mm"
include "syl7bi.mm"
include "impr.mm"
include "adantlr.mm"
include "ralrimiv.mm"
include "expr.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "wex.mm"
include "n0.mm"
include "fnfvima.mm"
include "mp3an12.mm"
include "ne0i.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "supsr.mm"
include "ex.mm"
include "notbid.mm"
include "rspccv.mm"
include "syl5com.mm"
include "simprbi.mm"
include "breq2d.mm"
include "ltresr.mm"
include "syl6bb.mm"
include "sylibrd.mm"
include "ralrimdva.mm"
include "ad2antrr.mm"
include "breq1d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "com3l.mm"
include "sylbid.mm"
include "adantr.mm"
include "sylan2.mm"
include "exbiri.mm"
include "com4r.mm"
include "imp.mm"
include "reximdvai.mm"
include "syl5bi.mm"
include "expcom.mm"
include "com23.mm"
include "rexlimdv.mm"
include "syl6d.mm"
include "ralrimdv.mm"
include "opelreal.mm"
include "biimpri.mm"
include "imbi1d.mm"
include "anbi12d.mm"
include "syl2and.mm"
include "3syld.mm"
include "3impia.mm"

theorem axpre-sup
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint v w
  disjoint u w
  disjoint A w
  disjoint u v
  disjoint A v
  disjoint A u
  assert |- ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y <RR x ) -> E. x e. RR ( A. y e. A -. x <RR y /\ A. y e. RR ( y <RR x -> E. z e. A y <RR z ) ) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cltrr
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cr
    wrex
    #
    @3
    @2
    cltrr
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @4
    @2
    vz
    cv
    #
    cltrr
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cr
    wral
    #
    wa
    #
    vx
    cr
    wrex
    #
    @0
    @1
    wa
    #
    @6
    vw
    cv
    #
    vv
    cv
    #
    cltr
    wbr
    #
    vw
    c1st
    cA
    cima
    #
    wral
    #
    vv
    cnr
    wrex
    #
    @19
    @18
    cltr
    wbr
    #
    wn
    #
    vw
    @21
    wral
    #
    @20
    @18
    vu
    cv
    #
    cltr
    wbr
    #
    vu
    @21
    wrex
    #
    wi
    #
    vw
    cnr
    wral
    #
    wa
    #
    vv
    cnr
    wrex
    #
    @16
    @17
    @5
    @23
    vx
    cr
    @17
    @3
    cr
    wcel
    #
    wa
    @3
    c1st
    cfv
    #
    cnr
    wcel
    #
    @5
    @18
    @35
    cltr
    wbr
    #
    vw
    @21
    wral
    #
    @23
    @34
    @36
    @17
    @34
    @36
    @3
    @35
    c0r
    cop
    wceq
    @3
    elreal2
    simplbi
    adantl
    @17
    @34
    @5
    @38
    @17
    @34
    @5
    wa
    #
    wa
    @37
    vw
    @21
    @0
    @39
    @18
    @21
    wcel
    #
    @37
    wi
    #
    @1
    @0
    @34
    @5
    @41
    @40
    @2
    c1st
    cfv
    #
    @18
    wceq
    #
    vy
    cA
    wrex
    #
    @0
    @34
    wa
    #
    @5
    @37
    c1st
    cvv
    wfn
    #
    cA
    cvv
    wss
    #
    @40
    @44
    wb
    cvv
    cvv
    c1st
    wfo
    cvv
    cvv
    c1st
    wf
    @46
    fo1st
    cvv
    cvv
    c1st
    fof
    cvv
    cvv
    c1st
    ffn
    mp2b
    #
    cA
    ssv
    #
    vy
    cvv
    cA
    @18
    c1st
    fvelimab
    mp2an
    @45
    @5
    @44
    @37
    @5
    @44
    wa
    @4
    @43
    wa
    #
    vy
    cA
    wrex
    @45
    @37
    @4
    @43
    vy
    cA
    r19.29
    @45
    @50
    @37
    vy
    cA
    @0
    @2
    cA
    wcel
    #
    @34
    @50
    @37
    wi
    @0
    @51
    wa
    #
    @34
    wa
    @43
    @4
    @37
    @52
    @34
    @43
    @4
    @37
    @52
    @2
    cr
    wcel
    #
    @34
    @43
    @4
    @37
    wi
    #
    wi
    wi
    cA
    cr
    @2
    ssel2
    #
    @53
    @34
    @43
    @54
    @53
    @34
    wa
    #
    @43
    wa
    @4
    @37
    @56
    @4
    @42
    @35
    cltr
    wbr
    @43
    @37
    @2
    @3
    ltresr2
    @42
    @18
    @35
    cltr
    breq1
    sylan9bb
    biimpd
    exp31
    syl
    imp4b
    ancomsd
    an32s
    rexlimdva
    syl5
    expd
    syl7bi
    impr
    adantlr
    ralrimiv
    expr
    @22
    @38
    vv
    @35
    cnr
    @19
    @35
    wceq
    @20
    @37
    vw
    @21
    @19
    @35
    @18
    cltr
    breq2
    ralbidv
    rspcev
    syl6an
    rexlimdva
    @1
    @23
    @33
    wi
    #
    @0
    @1
    @21
    c0
    wne
    #
    @57
    @1
    @51
    vy
    wex
    @58
    vy
    cA
    n0
    @51
    @58
    vy
    @51
    @42
    @21
    wcel
    #
    @58
    @46
    @47
    @51
    @59
    @48
    @49
    cvv
    cA
    c1st
    @2
    fnfvima
    mp3an12
    #
    @21
    @42
    ne0i
    syl
    exlimiv
    sylbi
    @58
    @23
    @33
    vv
    vw
    vu
    @21
    supsr
    ex
    syl
    adantl
    @17
    @32
    @16
    vv
    cnr
    @17
    @19
    cnr
    wcel
    #
    wa
    #
    @26
    @19
    c0r
    cop
    #
    @2
    cltrr
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @31
    @2
    @63
    cltrr
    wbr
    #
    @12
    wi
    #
    vy
    cr
    wral
    #
    @16
    @0
    @26
    @66
    wi
    @1
    @61
    @0
    @26
    @65
    vy
    cA
    @52
    @26
    @19
    @42
    cltr
    wbr
    #
    wn
    #
    @65
    @51
    @26
    @71
    wi
    @0
    @51
    @59
    @26
    @71
    @60
    @25
    @71
    vw
    @42
    @21
    @18
    @42
    wceq
    #
    @24
    @70
    @18
    @42
    @19
    cltr
    breq2
    notbid
    rspccv
    syl5com
    adantl
    @52
    @64
    @70
    @52
    @53
    @64
    @70
    wb
    @55
    @53
    @64
    @63
    @42
    c0r
    cop
    #
    cltrr
    wbr
    @70
    @53
    @2
    @73
    @63
    cltrr
    @53
    @42
    cnr
    wcel
    #
    @2
    @73
    wceq
    #
    @2
    elreal2
    #
    simprbi
    #
    breq2d
    @19
    @42
    ltresr
    syl6bb
    syl
    notbid
    sylibrd
    ralrimdva
    ad2antrr
    @62
    @31
    @68
    vy
    cr
    @0
    @31
    @53
    @68
    wi
    wi
    @1
    @61
    @53
    @0
    @31
    @68
    @53
    @0
    @31
    @68
    wi
    @53
    @0
    wa
    #
    @67
    @31
    @12
    @78
    @67
    @31
    @42
    @27
    cltr
    wbr
    #
    vu
    @21
    wrex
    #
    @12
    @53
    @67
    @31
    @80
    wi
    #
    wi
    @0
    @53
    @67
    @42
    @19
    cltr
    wbr
    #
    @81
    @53
    @67
    @73
    @63
    cltrr
    wbr
    @82
    @53
    @2
    @73
    @63
    cltrr
    @77
    breq1d
    @42
    @19
    ltresr
    syl6bb
    @31
    @53
    @82
    @80
    @53
    @74
    @31
    @82
    @80
    wi
    #
    @53
    @74
    @75
    @76
    simplbi
    @30
    @83
    vw
    @42
    cnr
    @72
    @20
    @82
    @29
    @80
    @18
    @42
    @19
    cltr
    breq1
    @72
    @28
    @79
    vu
    @21
    @18
    @42
    @27
    cltr
    breq1
    rexbidv
    imbi12d
    rspccv
    syl5
    com3l
    sylbid
    adantr
    @78
    @79
    @12
    vu
    @21
    @78
    @79
    @27
    @21
    wcel
    #
    @12
    @79
    @78
    @84
    @12
    wi
    @84
    @10
    c1st
    cfv
    #
    @27
    wceq
    #
    vz
    cA
    wrex
    #
    @79
    @78
    wa
    #
    @12
    @46
    @47
    @84
    @87
    wb
    @48
    @49
    vz
    cvv
    cA
    @27
    c1st
    fvelimab
    mp2an
    @88
    @86
    @11
    vz
    cA
    @79
    @78
    @10
    cA
    wcel
    #
    @86
    @11
    wi
    wi
    @78
    @89
    @86
    @79
    @11
    @53
    @0
    @89
    @86
    @79
    @11
    wi
    wi
    @53
    @0
    @89
    wa
    #
    wa
    #
    @86
    @11
    @79
    @91
    @11
    @42
    @85
    cltr
    wbr
    #
    @86
    @79
    @90
    @53
    @10
    cr
    wcel
    @11
    @92
    wb
    cA
    cr
    @10
    ssel2
    @2
    @10
    ltresr2
    sylan2
    @85
    @27
    @42
    cltr
    breq2
    sylan9bb
    exbiri
    expr
    com4r
    imp
    reximdvai
    syl5bi
    expcom
    com23
    rexlimdv
    syl6d
    com23
    ex
    com3l
    ad2antrr
    ralrimdv
    @62
    @63
    cr
    wcel
    #
    @66
    @69
    wa
    #
    @16
    wi
    @61
    @93
    @17
    @93
    @61
    @19
    opelreal
    biimpri
    adantl
    @93
    @94
    @16
    @15
    @94
    vx
    @63
    cr
    @3
    @63
    wceq
    #
    @9
    @66
    @14
    @69
    @95
    @8
    @65
    vy
    cA
    @95
    @7
    @64
    @3
    @63
    @2
    cltrr
    breq1
    notbid
    ralbidv
    @95
    @13
    @68
    vy
    cr
    @95
    @4
    @67
    @12
    @3
    @63
    @2
    cltrr
    breq2
    imbi1d
    ralbidv
    anbi12d
    rspcev
    ex
    syl
    syl2and
    rexlimdva
    3syld
    3impia
end
