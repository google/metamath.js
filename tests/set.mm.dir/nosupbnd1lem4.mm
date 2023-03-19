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
include "c0.mm"
include "c2o.mm"
include "wi.mm"
include "wne.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "simpl3.mm"
include "simprr.mm"
include "simp2l.mm"
include "simp3l.mm"
include "sseldd.mm"
include "simpl2l.mm"
include "wor.mm"
include "sltso.mm"
include "soasym.mm"
include "mpan.mm"
include "syl2an2r.mm"
include "mpd.mm"
include "jca.mm"
include "nosupbnd1lem2.mm"
include "syl112anc.mm"
include "nosupbnd1lem3.mm"
include "neneqd.mm"
include "expr.mm"
include "imnan.mm"
include "sylib.mm"
include "nrexdv.mm"
include "simpl3l.mm"
include "weq.mm"
include "breq2.mm"
include "cbvrexv.mm"
include "breq1.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "cbvralv.mm"
include "dfrex2.mm"
include "ralbii.mm"
include "ralnex.mm"
include "3bitri.mm"
include "sylibr.mm"
include "rspcv.mm"
include "sylc.mm"
include "con0.mm"
include "adantr.mm"
include "nosupno.mm"
include "3ad2ant2.mm"
include "nodmon.mm"
include "syl.mm"
include "simpl3r.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simpll3.mm"
include "eqtr4d.mm"
include "simplr.mm"
include "nolt02o.mm"
include "syl321anc.mm"
include "ancld.mm"
include "reximdva.mm"
include "mtand.mm"
include "neqned.mm"

theorem nosupbnd1lem4
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cU: class U
  let vg: setvar g
  let vw: setvar w
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
  disjoint U u
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint A w
  disjoint S w
  disjoint u w
  disjoint U w
  disjoint v w
  disjoint w x
  disjoint w y
  assert |- ( ( -. E. x e. A A. y e. A -. x <s y /\ ( A C_ No /\ A e. _V ) /\ ( U e. A /\ ( U |` dom S ) = S ) ) -> ( U ` dom S ) =/= (/) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cslt
    wbr
    #
    wn
    vy
    cA
    wral
    #
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
    @9
    cU
    cfv
    #
    c0
    @13
    @14
    c0
    wceq
    #
    cU
    vw
    cv
    #
    cslt
    wbr
    #
    @9
    @16
    cfv
    #
    c2o
    wceq
    #
    wa
    #
    vw
    cA
    wrex
    #
    @13
    @20
    vw
    cA
    @13
    @16
    cA
    wcel
    #
    wa
    @17
    @19
    wn
    #
    wi
    @20
    wn
    @13
    @22
    @17
    @23
    @13
    @22
    @17
    wa
    #
    wa
    #
    @18
    c2o
    @25
    @4
    @7
    @22
    @16
    @9
    cres
    #
    cS
    wceq
    #
    @18
    c2o
    wne
    @4
    @7
    @12
    @24
    simpl1
    #
    @4
    @7
    @12
    @24
    simpl2
    #
    @13
    @22
    @17
    simprl
    #
    @25
    @4
    @7
    @12
    @22
    @16
    cU
    cslt
    wbr
    wn
    #
    wa
    #
    @27
    @28
    @29
    @4
    @7
    @12
    @24
    simpl3
    @25
    @22
    @31
    @30
    @25
    @17
    @31
    @13
    @22
    @17
    simprr
    @13
    cU
    csur
    wcel
    #
    @24
    @16
    csur
    wcel
    #
    @17
    @31
    wi
    #
    @13
    cA
    csur
    cU
    @4
    @5
    @6
    @12
    simp2l
    @4
    @7
    @8
    @11
    simp3l
    sseldd
    @25
    cA
    csur
    @16
    @5
    @6
    @4
    @12
    @24
    simpl2l
    @30
    sseldd
    csur
    cslt
    wor
    @33
    @34
    wa
    @35
    sltso
    csur
    cslt
    cU
    @16
    soasym
    mpan
    #
    syl2an2r
    mpd
    jca
    vx
    vy
    vv
    vu
    cA
    cS
    cU
    vg
    @16
    nosupbnd1.1
    nosupbnd1lem2
    #
    syl112anc
    vx
    vy
    vv
    vu
    cA
    cS
    @16
    vg
    nosupbnd1.1
    nosupbnd1lem3
    syl112anc
    neneqd
    expr
    @17
    @19
    imnan
    sylib
    nrexdv
    @13
    @15
    wa
    #
    @17
    vw
    cA
    wrex
    #
    @21
    @38
    @8
    vu
    cv
    #
    @16
    cslt
    wbr
    #
    vw
    cA
    wrex
    #
    vu
    cA
    wral
    #
    @39
    @8
    @11
    @4
    @7
    @15
    simpl3l
    #
    @38
    @4
    @43
    @4
    @7
    @12
    @15
    simpl1
    @43
    @2
    vy
    cA
    wrex
    #
    vx
    cA
    wral
    @3
    wn
    #
    vx
    cA
    wral
    @4
    @42
    @45
    vu
    vx
    cA
    @42
    @40
    @1
    cslt
    wbr
    #
    vy
    cA
    wrex
    vu
    vx
    weq
    #
    @45
    @41
    @47
    vw
    vy
    cA
    @16
    @1
    @40
    cslt
    breq2
    cbvrexv
    @48
    @47
    @2
    vy
    cA
    @40
    @0
    @1
    cslt
    breq1
    rexbidv
    syl5bb
    cbvralv
    @45
    @46
    vx
    cA
    @2
    vy
    cA
    dfrex2
    ralbii
    @3
    vx
    cA
    ralnex
    3bitri
    sylibr
    @42
    @39
    vu
    cU
    cA
    @40
    cU
    wceq
    @41
    @17
    vw
    cA
    @40
    cU
    @16
    cslt
    breq1
    rexbidv
    rspcv
    sylc
    @38
    @17
    @20
    vw
    cA
    @38
    @22
    wa
    @17
    @19
    @38
    @22
    @17
    @19
    @38
    @24
    wa
    #
    @33
    @34
    @9
    con0
    wcel
    #
    @10
    @26
    wceq
    @17
    @15
    @19
    @38
    @33
    @24
    @38
    cA
    csur
    cU
    @5
    @6
    @4
    @12
    @15
    simpl2l
    #
    @44
    sseldd
    #
    adantr
    @49
    cA
    csur
    @16
    @38
    @5
    @24
    @51
    adantr
    @38
    @22
    @17
    simprl
    #
    sseldd
    #
    @49
    cS
    csur
    wcel
    #
    @50
    @38
    @55
    @24
    @13
    @55
    @15
    @7
    @4
    @55
    @12
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
    adantr
    adantr
    cS
    nodmon
    syl
    @49
    @10
    cS
    @26
    @38
    @11
    @24
    @8
    @11
    @4
    @7
    @15
    simpl3r
    adantr
    @49
    @4
    @7
    @12
    @32
    @27
    @4
    @7
    @12
    @15
    @24
    simpll1
    @4
    @7
    @12
    @15
    @24
    simpll2
    @4
    @7
    @12
    @15
    @24
    simpll3
    @49
    @22
    @31
    @53
    @49
    @17
    @31
    @38
    @22
    @17
    simprr
    #
    @38
    @33
    @24
    @34
    @35
    @52
    @54
    @36
    syl2an2r
    mpd
    jca
    @37
    syl112anc
    eqtr4d
    @56
    @13
    @15
    @24
    simplr
    cU
    @16
    @9
    nolt02o
    syl321anc
    expr
    ancld
    reximdva
    mpd
    mtand
    neqned
end
