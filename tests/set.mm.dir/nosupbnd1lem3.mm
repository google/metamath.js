include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "csur.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "cfv.mm"
include "c2o.mm"
include "word.mm"
include "nosupno.mm"
include "3ad2ant2.mm"
include "nodmord.mm"
include "ordirr.mm"
include "3syl.mm"
include "csuc.mm"
include "wi.mm"
include "simpl3l.mm"
include "c0.mm"
include "ndmfv.mm"
include "wne.mm"
include "c1o.mm"
include "con0.mm"
include "2on.mm"
include "elexi.mm"
include "prid2.mm"
include "nosgnn0i.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "neneqd.mm"
include "syl.mm"
include "con4i.mm"
include "adantl.mm"
include "simpl2l.mm"
include "adantr.mm"
include "sseldd.mm"
include "simprl.mm"
include "nodmon.mm"
include "simpl3r.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simpll3.mm"
include "simpr.mm"
include "nosupbnd1lem2.mm"
include "syl112anc.mm"
include "eqtr4d.mm"
include "simplr.mm"
include "simprr.mm"
include "nolesgn2ores.mm"
include "syl321anc.mm"
include "expr.mm"
include "ralrimiva.mm"
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
include "wb.mm"
include "cab.mm"
include "nosupdm.mm"
include "3ad2ant1.mm"
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

theorem nosupbnd1lem3
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cU: class U
  let vg: setvar g
  let vp: setvar p
  let vq: setvar q
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
  disjoint A p
  disjoint A q
  disjoint A z
  disjoint p q
  disjoint p u
  disjoint p v
  disjoint p y
  disjoint p z
  disjoint q u
  disjoint q v
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint S p
  disjoint S q
  disjoint S z
  disjoint U p
  disjoint U q
  disjoint u z
  disjoint v z
  disjoint y z
  assert |- ( ( -. E. x e. A A. y e. A -. x <s y /\ ( A C_ No /\ A e. _V ) /\ ( U e. A /\ ( U |` dom S ) = S ) ) -> ( U ` dom S ) =/= 2o )

  proof
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
    cS
    cdm
    #
    cres
    #
    cS
    wceq
    #
    wa
    #
    w3a
    #
    @5
    cU
    cfv
    #
    c2o
    @9
    @10
    c2o
    wceq
    #
    @5
    @5
    wcel
    #
    @9
    cS
    csur
    wcel
    #
    @5
    word
    @12
    wn
    @3
    @0
    @13
    @8
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
    #
    cS
    nodmord
    @5
    ordirr
    3syl
    @9
    @11
    wa
    #
    @12
    @5
    vp
    cv
    #
    cdm
    #
    wcel
    #
    vq
    cv
    #
    @16
    cslt
    wbr
    #
    wn
    #
    @16
    @5
    csuc
    #
    cres
    #
    @19
    @22
    cres
    #
    wceq
    #
    wi
    #
    vq
    cA
    wral
    #
    wa
    #
    vp
    cA
    wrex
    #
    @15
    @4
    @5
    cU
    cdm
    #
    wcel
    #
    @19
    cU
    cslt
    wbr
    #
    wn
    #
    cU
    @22
    cres
    #
    @24
    wceq
    #
    wi
    #
    vq
    cA
    wral
    #
    @29
    @4
    @7
    @0
    @3
    @11
    simpl3l
    #
    @11
    @31
    @9
    @31
    @11
    @31
    wn
    @10
    c0
    wceq
    #
    @11
    wn
    @5
    cU
    ndmfv
    @39
    @10
    c2o
    @39
    @10
    c2o
    wne
    c0
    c2o
    wne
    c2o
    c1o
    c2o
    c2o
    con0
    2on
    elexi
    prid2
    nosgnn0i
    @10
    c0
    c2o
    neeq1
    mpbiri
    neneqd
    syl
    con4i
    adantl
    @15
    @36
    vq
    cA
    @15
    @19
    cA
    wcel
    #
    @33
    @35
    @15
    @40
    @33
    wa
    #
    wa
    #
    cU
    csur
    wcel
    @19
    csur
    wcel
    @5
    con0
    wcel
    #
    @6
    @19
    @5
    cres
    #
    wceq
    @11
    @33
    @35
    @42
    cA
    csur
    cU
    @15
    @1
    @41
    @1
    @2
    @0
    @8
    @11
    simpl2l
    adantr
    #
    @15
    @4
    @41
    @38
    adantr
    sseldd
    @42
    cA
    csur
    @19
    @45
    @15
    @40
    @33
    simprl
    sseldd
    @42
    @13
    @43
    @15
    @13
    @41
    @9
    @13
    @11
    @14
    adantr
    adantr
    cS
    nodmon
    #
    syl
    @42
    @6
    cS
    @44
    @15
    @7
    @41
    @4
    @7
    @0
    @3
    @11
    simpl3r
    adantr
    @42
    @0
    @3
    @8
    @41
    @44
    cS
    wceq
    @0
    @3
    @8
    @11
    @41
    simpll1
    @0
    @3
    @8
    @11
    @41
    simpll2
    @0
    @3
    @8
    @11
    @41
    simpll3
    @15
    @41
    simpr
    vx
    vy
    vv
    vu
    cA
    cS
    cU
    vg
    @19
    nosupbnd1.1
    nosupbnd1lem2
    syl112anc
    eqtr4d
    @9
    @11
    @41
    simplr
    @15
    @40
    @33
    simprr
    cU
    @19
    @5
    nolesgn2ores
    syl321anc
    expr
    ralrimiva
    @28
    @31
    @37
    wa
    vp
    cU
    cA
    @16
    cU
    wceq
    #
    @18
    @31
    @27
    @37
    @47
    @17
    @30
    @5
    @16
    cU
    dmeq
    eleq2d
    @47
    @26
    @36
    vq
    cA
    @47
    @21
    @33
    @25
    @35
    @47
    @20
    @32
    @16
    cU
    @19
    cslt
    breq2
    notbid
    @47
    @23
    @34
    @24
    @16
    cU
    @22
    reseq1
    eqeq1d
    imbi12d
    ralbidv
    anbi12d
    rspcev
    syl12anc
    @9
    @12
    @29
    wb
    @11
    @9
    @12
    @5
    vz
    cv
    #
    @17
    wcel
    #
    @21
    @16
    @48
    csuc
    #
    cres
    #
    @19
    @50
    cres
    #
    wceq
    #
    wi
    #
    vq
    cA
    wral
    #
    wa
    #
    vp
    cA
    wrex
    #
    vz
    cab
    #
    wcel
    #
    @29
    @0
    @3
    @12
    @59
    wb
    @8
    @0
    @5
    @58
    @5
    vx
    vy
    vz
    vv
    vu
    cA
    cS
    vg
    vq
    vp
    nosupbnd1.1
    nosupdm
    eleq2d
    3ad2ant1
    @9
    @13
    @43
    @59
    @29
    wb
    @14
    @46
    @57
    @29
    vz
    @5
    con0
    @48
    @5
    wceq
    #
    @56
    @28
    vp
    cA
    @60
    @49
    @18
    @55
    @27
    @48
    @5
    @17
    eleq1
    @60
    @54
    @26
    vq
    cA
    @60
    @53
    @25
    @21
    @60
    @51
    @23
    @52
    @24
    @60
    @50
    @22
    @16
    @48
    @5
    suceq
    #
    reseq2d
    @60
    @50
    @22
    @19
    @61
    reseq2d
    eqeq12d
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    elabg
    3syl
    bitrd
    adantr
    mpbird
    mtand
    neqned
end
