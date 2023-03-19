include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "cdm.mm"
include "cfv.mm"
include "c1o.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "csur.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "w3a.mm"
include "wne.mm"
include "word.mm"
include "nosupno.mm"
include "3ad2ant2.mm"
include "adantl.mm"
include "nodmord.mm"
include "ordirr.mm"
include "3syl.mm"
include "csuc.mm"
include "simpr3l.mm"
include "adantr.mm"
include "c0.mm"
include "ndmfv.mm"
include "c2o.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "prid1.mm"
include "nosgnn0i.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "neneqd.mm"
include "syl.mm"
include "con4i.mm"
include "wfun.mm"
include "simp2l.mm"
include "simp3l.mm"
include "sseldd.mm"
include "nofun.mm"
include "simpl2l.mm"
include "simpll.mm"
include "ssel2.mm"
include "syl2an.mm"
include "simpl3r.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simpll3.mm"
include "simprl.mm"
include "nosupbnd1lem2.mm"
include "syl112anc.mm"
include "eqtr4d.mm"
include "simplr.mm"
include "simprr.mm"
include "eqfunressuc.mm"
include "syl213anc.mm"
include "expr.mm"
include "a2d.mm"
include "ralimdva.mm"
include "impcom.mm"
include "anassrs.mm"
include "dmeq.mm"
include "eleq2d.mm"
include "breq2.mm"
include "notbid.mm"
include "reseq1.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "cab.mm"
include "wb.mm"
include "simplr1.mm"
include "nosupdm.mm"
include "nodmon.mm"
include "eleq1.mm"
include "suceq.mm"
include "reseq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "rexbidv.mm"
include "elabg.mm"
include "bitrd.mm"
include "mpbird.mm"
include "mtand.mm"
include "neqned.mm"
include "rexanali.mm"
include "wo.mm"
include "w3o.mm"
include "simpl.mm"
include "nofv.mm"
include "3orel2.mm"
include "syl5com.mm"
include "imdistanda.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "nosupbnd1lem4.mm"
include "pm2.21d.mm"
include "nosupbnd1lem3.mm"
include "jaod.mm"
include "expimpd.mm"
include "syldc.mm"
include "anasss.mm"
include "rexlimiva.mm"
include "imp.mm"
include "sylanbr.mm"
include "pm2.61ian.mm"

theorem nosupbnd1lem5
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cU: class U
  let vg: setvar g
  let va: setvar a
  let vp: setvar p
  let vz: setvar z
  assume nosupbnd1.1: |- S = if ( E. x e. A A. y e. A -. x <s y , ( ( iota_ x e. A A. y e. A -. x <s y ) u. { <. dom ( iota_ x e. A A. y e. A -. x <s y ) , 2o >. } ) , ( g e. { y | E. u e. A ( y e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc y ) = ( v |` suc y ) ) ) } |-> ( iota x E. u e. A ( g e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc g ) = ( v |` suc g ) ) /\ ( u ` g ) = x ) ) ) )

  disjoint A g
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint A a
  disjoint a p
  disjoint A p
  disjoint a u
  disjoint a v
  disjoint a y
  disjoint a z
  disjoint A z
  disjoint p u
  disjoint p v
  disjoint p y
  disjoint p z
  disjoint S a
  disjoint S p
  disjoint S z
  disjoint U p
  disjoint u z
  disjoint U z
  disjoint v z
  disjoint x z
  disjoint y z
  assert |- ( ( -. E. x e. A A. y e. A -. x <s y /\ ( A C_ No /\ A e. _V ) /\ ( U e. A /\ ( U |` dom S ) = S ) ) -> ( U ` dom S ) =/= 1o )

  proof
    vz
    cv
    #
    cU
    cslt
    wbr
    #
    wn
    #
    cS
    cdm
    #
    @0
    cfv
    #
    c1o
    wceq
    #
    wi
    #
    vz
    cA
    wral
    #
    vx
    cv
    vy
    cv
    cslt
    wbr
    wn
    vy
    cA
    wral
    vx
    cA
    wrex
    wn
    #
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    wa
    #
    cU
    cA
    wcel
    #
    cU
    @3
    cres
    #
    cS
    wceq
    #
    wa
    #
    w3a
    #
    @3
    cU
    cfv
    #
    c1o
    wne
    #
    @7
    @16
    wa
    #
    @17
    c1o
    @19
    @17
    c1o
    wceq
    #
    @3
    @3
    wcel
    #
    @19
    cS
    csur
    wcel
    #
    @3
    word
    @21
    wn
    @16
    @22
    @7
    @11
    @8
    @22
    @15
    vx
    vy
    vv
    vu
    cA
    cS
    vg
    cvv
    nosupbnd1.1
    nosupno
    3ad2ant2
    adantl
    #
    cS
    nodmord
    @3
    ordirr
    3syl
    @19
    @20
    wa
    #
    @21
    @3
    vp
    cv
    #
    cdm
    #
    wcel
    #
    @0
    @25
    cslt
    wbr
    #
    wn
    #
    @25
    @3
    csuc
    #
    cres
    #
    @0
    @30
    cres
    #
    wceq
    #
    wi
    #
    vz
    cA
    wral
    #
    wa
    #
    vp
    cA
    wrex
    #
    @24
    @12
    @3
    cU
    cdm
    #
    wcel
    #
    @2
    cU
    @30
    cres
    #
    @32
    wceq
    #
    wi
    #
    vz
    cA
    wral
    #
    @37
    @19
    @12
    @20
    @12
    @14
    @8
    @11
    @7
    simpr3l
    adantr
    @20
    @39
    @19
    @39
    @20
    @39
    wn
    @17
    c0
    wceq
    #
    @20
    wn
    @3
    cU
    ndmfv
    @44
    @17
    c1o
    @44
    @18
    c0
    c1o
    wne
    #
    c1o
    c1o
    c2o
    c1o
    con0
    1on
    elexi
    prid1
    nosgnn0i
    #
    @17
    c0
    c1o
    neeq1
    mpbiri
    neneqd
    syl
    con4i
    #
    adantl
    @7
    @16
    @20
    @43
    @16
    @20
    wa
    #
    @7
    @43
    @48
    @6
    @42
    vz
    cA
    @48
    @0
    cA
    wcel
    #
    wa
    @2
    @5
    @41
    @48
    @49
    @2
    @5
    @41
    wi
    @48
    @49
    @2
    wa
    #
    @5
    @41
    @48
    @50
    @5
    wa
    #
    wa
    #
    cU
    wfun
    #
    @0
    wfun
    #
    @13
    @0
    @3
    cres
    #
    wceq
    @39
    @3
    @0
    cdm
    wcel
    #
    @17
    @4
    wceq
    @41
    @52
    cU
    csur
    wcel
    #
    @53
    @48
    @57
    @51
    @16
    @57
    @20
    @16
    cA
    csur
    cU
    @8
    @9
    @10
    @15
    simp2l
    #
    @8
    @11
    @12
    @14
    simp3l
    sseldd
    adantr
    adantr
    cU
    nofun
    syl
    @52
    @0
    csur
    wcel
    #
    @54
    @48
    @9
    @49
    @59
    @51
    @9
    @10
    @8
    @15
    @20
    simpl2l
    @49
    @2
    @5
    simpll
    cA
    csur
    @0
    ssel2
    #
    syl2an
    @0
    nofun
    syl
    @52
    @13
    cS
    @55
    @48
    @14
    @51
    @12
    @14
    @8
    @11
    @20
    simpl3r
    adantr
    @52
    @8
    @11
    @15
    @50
    @55
    cS
    wceq
    #
    @8
    @11
    @15
    @20
    @51
    simpll1
    @8
    @11
    @15
    @20
    @51
    simpll2
    @8
    @11
    @15
    @20
    @51
    simpll3
    @48
    @50
    @5
    simprl
    vx
    vy
    vv
    vu
    cA
    cS
    cU
    vg
    @0
    nosupbnd1.1
    nosupbnd1lem2
    #
    syl112anc
    eqtr4d
    @48
    @39
    @51
    @20
    @39
    @16
    @47
    adantl
    adantr
    @51
    @56
    @48
    @5
    @56
    @50
    @56
    @5
    @56
    wn
    @4
    c0
    wceq
    #
    @5
    wn
    #
    @3
    @0
    ndmfv
    @63
    @4
    c1o
    @63
    @4
    c1o
    wne
    @45
    @46
    @4
    c0
    c1o
    neeq1
    mpbiri
    neneqd
    syl
    con4i
    adantl
    adantl
    @52
    @17
    c1o
    @4
    @16
    @20
    @51
    simplr
    @48
    @50
    @5
    simprr
    eqtr4d
    cU
    @0
    @3
    eqfunressuc
    syl213anc
    expr
    expr
    a2d
    ralimdva
    impcom
    anassrs
    @36
    @39
    @43
    wa
    vp
    cU
    cA
    @25
    cU
    wceq
    #
    @27
    @39
    @35
    @43
    @65
    @26
    @38
    @3
    @25
    cU
    dmeq
    eleq2d
    @65
    @34
    @42
    vz
    cA
    @65
    @29
    @2
    @33
    @41
    @65
    @28
    @1
    @25
    cU
    @0
    cslt
    breq2
    notbid
    @65
    @31
    @40
    @32
    @25
    cU
    @30
    reseq1
    eqeq1d
    imbi12d
    ralbidv
    anbi12d
    rspcev
    syl12anc
    @24
    @21
    @3
    va
    cv
    #
    @26
    wcel
    #
    @29
    @25
    @66
    csuc
    #
    cres
    #
    @0
    @68
    cres
    #
    wceq
    #
    wi
    #
    vz
    cA
    wral
    #
    wa
    #
    vp
    cA
    wrex
    #
    va
    cab
    #
    wcel
    #
    @37
    @24
    @8
    @21
    @77
    wb
    @8
    @11
    @15
    @7
    @20
    simplr1
    @8
    @3
    @76
    @3
    vx
    vy
    va
    vv
    vu
    cA
    cS
    vg
    vz
    vp
    nosupbnd1.1
    nosupdm
    eleq2d
    syl
    @24
    @22
    @3
    con0
    wcel
    @77
    @37
    wb
    @19
    @22
    @20
    @23
    adantr
    cS
    nodmon
    @75
    @37
    va
    @3
    con0
    @66
    @3
    wceq
    #
    @74
    @36
    vp
    cA
    @78
    @67
    @27
    @73
    @35
    @66
    @3
    @26
    eleq1
    @78
    @72
    @34
    vz
    cA
    @78
    @71
    @33
    @29
    @78
    @69
    @31
    @70
    @32
    @78
    @68
    @30
    @25
    @66
    @3
    suceq
    #
    reseq2d
    @78
    @68
    @30
    @0
    @79
    reseq2d
    eqeq12d
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    elabg
    3syl
    bitrd
    mpbird
    mtand
    neqned
    @7
    wn
    @2
    @64
    wa
    #
    vz
    cA
    wrex
    #
    @16
    @18
    @2
    @5
    vz
    cA
    rexanali
    @81
    @16
    @18
    @80
    @16
    @18
    wi
    #
    vz
    cA
    @49
    @2
    @64
    @82
    @16
    @50
    @64
    wa
    @50
    @63
    @4
    c2o
    wceq
    #
    wo
    #
    wa
    @18
    @16
    @50
    @64
    @84
    @16
    @50
    wa
    #
    @63
    @5
    @83
    w3o
    #
    @64
    @84
    @85
    @59
    @86
    @16
    @9
    @49
    @59
    @50
    @58
    @49
    @2
    simpl
    @60
    syl2an
    @0
    @3
    nofv
    syl
    @63
    @5
    @83
    3orel2
    syl5com
    imdistanda
    @16
    @50
    @84
    @18
    @85
    @63
    @18
    @83
    @85
    @63
    @18
    @85
    @4
    c0
    @85
    @8
    @11
    @49
    @61
    @4
    c0
    wne
    @8
    @11
    @15
    @50
    simpl1
    #
    @8
    @11
    @15
    @50
    simpl2
    #
    @16
    @49
    @2
    simprl
    #
    @85
    @8
    @11
    @15
    @50
    @61
    @87
    @88
    @8
    @11
    @15
    @50
    simpl3
    @16
    @50
    simpr
    @62
    syl112anc
    #
    vx
    vy
    vv
    vu
    cA
    cS
    @0
    vg
    nosupbnd1.1
    nosupbnd1lem4
    syl112anc
    neneqd
    pm2.21d
    @85
    @83
    @18
    @85
    @4
    c2o
    @85
    @8
    @11
    @49
    @61
    @4
    c2o
    wne
    @87
    @88
    @89
    @90
    vx
    vy
    vv
    vu
    cA
    cS
    @0
    vg
    nosupbnd1.1
    nosupbnd1lem3
    syl112anc
    neneqd
    pm2.21d
    jaod
    expimpd
    syldc
    anasss
    rexlimiva
    imp
    sylanbr
    pm2.61ian
end
