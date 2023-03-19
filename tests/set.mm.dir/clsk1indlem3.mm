include "cv.mm"
include "cun.mm"
include "cfv.mm"
include "wss.mm"
include "c3o.mm"
include "cpw.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "csn.mm"
include "wceq.mm"
include "c1o.mm"
include "cpr.mm"
include "cif.mm"
include "wn.mm"
include "wel.mm"
include "wo.mm"
include "elif.mm"
include "wi.mm"
include "uneq12.mm"
include "unidm.mm"
include "syl6eq.mm"
include "an3.mm"
include "orcd.mm"
include "ex.mm"
include "pm2.24.mm"
include "impd.mm"
include "jaao.mm"
include "mpdan.mm"
include "a1i.mm"
include "w3o.mm"
include "uneqsn.mm"
include "df-3or.mm"
include "bitri.mm"
include "pm2.21.mm"
include "adantrd.mm"
include "jaod.mm"
include "adantr.mm"
include "adantl.mm"
include "adantld.mm"
include "syl5bi.mm"
include "elun.mm"
include "biimpi.mm"
include "andi.mm"
include "simpl.mm"
include "anim1i.mm"
include "simpr.mm"
include "orim12i.mm"
include "sylbi.mm"
include "sylan2.mm"
include "olcd.mm"
include "or4.mm"
include "sylib.mm"
include "orc.mm"
include "expcom.mm"
include "id.mm"
include "snsspr1.mm"
include "syl6eqss.mm"
include "sseld.mm"
include "impcom.mm"
include "jca.mm"
include "olc.mm"
include "jaoa.mm"
include "jaoi.mm"
include "anc2li.mm"
include "orim12d.mm"
include "com12.mm"
include "or42.mm"
include "syl6ib.mm"
include "4exmid.mm"
include "mpjaod.mm"
include "orbi12i.mm"
include "sylbbr.mm"
include "syl6.mm"
include "ssrdv.mm"
include "con0.mm"
include "3on.mm"
include "elpwi.mm"
include "unss.mm"
include "syl2an.mm"
include "sselpwd.mm"
include "eqeq1.mm"
include "ifbieq2d.mm"
include "prex.mm"
include "vex.mm"
include "unex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "syl.mm"
include "weq.mm"
include "uneq12d.mm"
include "3sstr4d.mm"
include "rgen2a.mm"

theorem clsk1indlem3
  let vt: setvar t
  let cK: class K
  let vs: setvar s
  let vr: setvar r
  let vx: setvar x
  assume clsk1indlem.k: |- K = ( r e. ~P 3o |-> if ( r = { (/) } , { (/) , 1o } , r ) )

  disjoint r s
  disjoint r t
  disjoint s t
  disjoint s x
  disjoint t x
  assert |- A. s e. ~P 3o A. t e. ~P 3o ( K ` ( s u. t ) ) C_ ( ( K ` s ) u. ( K ` t ) )

  proof
    vs
    cv
    #
    vt
    cv
    #
    cun
    #
    cK
    cfv
    #
    @0
    cK
    cfv
    #
    @1
    cK
    cfv
    #
    cun
    #
    wss
    vs
    vt
    c3o
    cpw
    #
    @0
    @7
    wcel
    #
    @1
    @7
    wcel
    #
    wa
    #
    @2
    c0
    csn
    #
    wceq
    #
    c0
    c1o
    cpr
    #
    @2
    cif
    #
    @0
    @11
    wceq
    #
    @13
    @0
    cif
    #
    @1
    @11
    wceq
    #
    @13
    @1
    cif
    #
    cun
    #
    @3
    @6
    @10
    vx
    @14
    @19
    @10
    vx
    cv
    #
    @14
    wcel
    #
    @15
    @20
    @13
    wcel
    #
    wa
    #
    @15
    wn
    #
    vx
    vs
    wel
    #
    wa
    #
    wo
    #
    @17
    @22
    wa
    #
    @17
    wn
    #
    vx
    vt
    wel
    #
    wa
    #
    wo
    #
    wo
    #
    @20
    @19
    wcel
    #
    @21
    @12
    @22
    wa
    #
    @12
    wn
    #
    @20
    @2
    wcel
    #
    wa
    #
    wo
    #
    @10
    @33
    @12
    @20
    @13
    @2
    elif
    @10
    @15
    @17
    wa
    #
    @24
    @29
    wa
    #
    wo
    #
    @39
    @33
    wi
    #
    @15
    @29
    wa
    #
    @17
    @24
    wa
    #
    wo
    #
    @10
    @40
    @43
    @41
    @40
    @43
    wi
    @10
    @40
    @12
    @43
    @40
    @2
    @11
    @11
    cun
    @11
    @0
    @11
    @1
    @11
    uneq12
    @11
    unidm
    syl6eq
    @40
    @35
    @33
    @12
    @38
    @40
    @35
    @33
    @40
    @35
    wa
    #
    @27
    @32
    @47
    @23
    @26
    @15
    @17
    @12
    @22
    an3
    orcd
    orcd
    ex
    @12
    @36
    @37
    @33
    @12
    @37
    @33
    wi
    pm2.24
    impd
    jaao
    mpdan
    a1i
    @41
    @43
    wi
    @10
    @41
    @35
    @33
    @38
    @41
    @12
    @22
    @33
    @12
    @40
    @15
    @1
    c0
    wceq
    #
    wa
    #
    wo
    #
    @0
    c0
    wceq
    #
    @17
    wa
    #
    wo
    #
    @41
    @22
    @33
    wi
    #
    @12
    @40
    @49
    @52
    w3o
    @53
    @0
    @1
    c0
    uneqsn
    @40
    @49
    @52
    df-3or
    bitri
    @41
    @50
    @54
    @52
    @24
    @50
    @54
    wi
    @29
    @24
    @40
    @54
    @49
    @24
    @15
    @54
    @17
    @15
    @54
    pm2.21
    #
    adantrd
    @24
    @15
    @54
    @48
    @55
    adantrd
    jaod
    adantr
    @41
    @17
    @54
    @51
    @29
    @17
    @54
    wi
    @24
    @17
    @54
    pm2.21
    adantl
    adantld
    jaod
    syl5bi
    impd
    @41
    @38
    @33
    @41
    @38
    wa
    #
    @23
    @28
    wo
    #
    @26
    @31
    wo
    #
    wo
    @33
    @56
    @58
    @57
    @38
    @41
    @25
    @30
    wo
    #
    @58
    @37
    @59
    @36
    @37
    @59
    @20
    @0
    @1
    elun
    #
    biimpi
    adantl
    @41
    @59
    wa
    @41
    @25
    wa
    #
    @41
    @30
    wa
    #
    wo
    @58
    @41
    @25
    @30
    andi
    @61
    @26
    @62
    @31
    @41
    @24
    @25
    @24
    @29
    simpl
    anim1i
    @41
    @29
    @30
    @24
    @29
    simpr
    anim1i
    orim12i
    sylbi
    sylan2
    olcd
    @23
    @28
    @26
    @31
    or4
    sylib
    ex
    jaod
    a1i
    jaod
    @46
    @43
    wi
    @10
    @46
    @39
    @23
    @31
    wo
    #
    @26
    @28
    wo
    #
    wo
    #
    @33
    @39
    @46
    @65
    @39
    @44
    @63
    @45
    @64
    @35
    @44
    @63
    wi
    #
    @38
    @22
    @66
    @12
    @22
    @15
    @63
    @29
    @15
    @22
    @63
    @23
    @31
    orc
    expcom
    adantrd
    adantl
    @37
    @66
    @36
    @37
    @59
    @66
    @60
    @25
    @15
    @63
    @30
    @29
    @25
    @15
    @63
    @25
    @15
    wa
    #
    @23
    @31
    @67
    @15
    @22
    @25
    @15
    simpr
    @15
    @25
    @22
    @15
    @0
    @13
    @20
    @15
    @0
    @11
    @13
    @15
    id
    c0
    c1o
    snsspr1
    #
    syl6eqss
    sseld
    impcom
    jca
    orcd
    ex
    @29
    @30
    @63
    @31
    @23
    olc
    expcom
    jaoa
    sylbi
    adantl
    jaoi
    @35
    @45
    @64
    wi
    #
    @38
    @35
    @17
    @64
    @24
    @22
    @17
    @64
    wi
    @12
    @17
    @22
    @64
    @28
    @26
    olc
    expcom
    adantl
    adantrd
    @37
    @69
    @36
    @37
    @59
    @69
    @60
    @45
    @59
    @64
    @45
    @25
    @26
    @30
    @28
    @24
    @25
    @26
    wi
    @17
    @24
    @25
    @26
    @26
    id
    ex
    adantl
    @17
    @30
    @28
    wi
    @24
    @17
    @30
    @22
    @17
    @1
    @13
    @20
    @17
    @1
    @11
    @13
    @17
    id
    @68
    syl6eqss
    sseld
    anc2li
    adantr
    orim12d
    com12
    sylbi
    adantl
    jaoi
    orim12d
    com12
    @23
    @31
    @26
    @28
    or42
    syl6ib
    a1i
    @42
    @46
    wo
    @10
    @15
    @17
    4exmid
    a1i
    mpjaod
    syl5bi
    @34
    @20
    @16
    wcel
    #
    @20
    @18
    wcel
    #
    wo
    @33
    @20
    @16
    @18
    elun
    @70
    @27
    @71
    @32
    @15
    @20
    @13
    @0
    elif
    @17
    @20
    @13
    @1
    elif
    orbi12i
    sylbbr
    syl6
    ssrdv
    @10
    @2
    @7
    wcel
    @3
    @14
    wceq
    @10
    @2
    c3o
    con0
    c3o
    con0
    wcel
    @10
    3on
    a1i
    @8
    @0
    c3o
    wss
    #
    @1
    c3o
    wss
    #
    @2
    c3o
    wss
    #
    @9
    @0
    c3o
    elpwi
    @1
    c3o
    elpwi
    @72
    @73
    wa
    @74
    @0
    @1
    c3o
    unss
    biimpi
    syl2an
    sselpwd
    vr
    @2
    vr
    cv
    #
    @11
    wceq
    #
    @13
    @75
    cif
    #
    @14
    @7
    cK
    @75
    @2
    wceq
    #
    @76
    @12
    @75
    @2
    @13
    @75
    @2
    @11
    eqeq1
    @78
    id
    ifbieq2d
    clsk1indlem.k
    @12
    @13
    @2
    c0
    c1o
    prex
    #
    @0
    @1
    vs
    vex
    #
    vt
    vex
    #
    unex
    ifex
    fvmpt
    syl
    @10
    @4
    @16
    @5
    @18
    @8
    @4
    @16
    wceq
    @9
    vr
    @0
    @77
    @16
    @7
    cK
    vr
    vs
    weq
    #
    @76
    @15
    @75
    @0
    @13
    @75
    @0
    @11
    eqeq1
    @82
    id
    ifbieq2d
    clsk1indlem.k
    @15
    @13
    @0
    @79
    @80
    ifex
    fvmpt
    adantr
    @9
    @5
    @18
    wceq
    @8
    vr
    @1
    @77
    @18
    @7
    cK
    vr
    vt
    weq
    #
    @76
    @17
    @75
    @1
    @13
    @75
    @1
    @11
    eqeq1
    @83
    id
    ifbieq2d
    clsk1indlem.k
    @17
    @13
    @1
    @79
    @81
    ifex
    fvmpt
    adantl
    uneq12d
    3sstr4d
    rgen2a
end
