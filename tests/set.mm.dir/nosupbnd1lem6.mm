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
include "w3a.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "cfv.mm"
include "c0.mm"
include "c1o.mm"
include "c2o.mm"
include "w3o.mm"
include "simp2l.mm"
include "simp3.mm"
include "sseldd.mm"
include "nofv.mm"
include "syl.mm"
include "3oran.mm"
include "sylib.mm"
include "wne.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "nosupbnd1lem4.mm"
include "syl112anc.mm"
include "neneqd.mm"
include "nosupbnd1lem5.mm"
include "nosupbnd1lem3.mm"
include "3jca.mm"
include "mtand.mm"
include "nosupbnd1lem1.mm"
include "con0.mm"
include "nosupno.mm"
include "3ad2ant2.mm"
include "nodmon.mm"
include "noreson.mm"
include "syl2anc.mm"
include "wor.mm"
include "sltso.mm"
include "solin.mm"
include "mpan.mm"
include "ecase23d.mm"

theorem nosupbnd1lem6
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cU: class U
  let vg: setvar g
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
  disjoint U v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  assert |- ( ( -. E. x e. A A. y e. A -. x <s y /\ ( A C_ No /\ A e. _V ) /\ U e. A ) -> ( U |` dom S ) <s S )

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
    w3a
    #
    cU
    cS
    cdm
    #
    cres
    #
    cS
    cslt
    wbr
    #
    @7
    cS
    wceq
    #
    cS
    @7
    cslt
    wbr
    #
    @5
    @9
    @6
    cU
    cfv
    #
    c0
    wceq
    #
    wn
    #
    @11
    c1o
    wceq
    #
    wn
    #
    @11
    c2o
    wceq
    #
    wn
    #
    w3a
    #
    @5
    @12
    @14
    @16
    w3o
    #
    @18
    wn
    @5
    cU
    csur
    wcel
    #
    @19
    @5
    cA
    csur
    cU
    @0
    @1
    @2
    @4
    simp2l
    @0
    @3
    @4
    simp3
    sseldd
    #
    cU
    @6
    nofv
    syl
    @12
    @14
    @16
    3oran
    sylib
    @5
    @9
    wa
    #
    @13
    @15
    @17
    @22
    @11
    c0
    @22
    @0
    @3
    @4
    @9
    @11
    c0
    wne
    @0
    @3
    @4
    @9
    simpl1
    #
    @0
    @3
    @4
    @9
    simpl2
    #
    @0
    @3
    @4
    @9
    simpl3
    #
    @5
    @9
    simpr
    #
    vx
    vy
    vv
    vu
    cA
    cS
    cU
    vg
    nosupbnd1.1
    nosupbnd1lem4
    syl112anc
    neneqd
    @22
    @11
    c1o
    @22
    @0
    @3
    @4
    @9
    @11
    c1o
    wne
    @23
    @24
    @25
    @26
    vx
    vy
    vv
    vu
    cA
    cS
    cU
    vg
    nosupbnd1.1
    nosupbnd1lem5
    syl112anc
    neneqd
    @22
    @11
    c2o
    @22
    @0
    @3
    @4
    @9
    @11
    c2o
    wne
    @23
    @24
    @25
    @26
    vx
    vy
    vv
    vu
    cA
    cS
    cU
    vg
    nosupbnd1.1
    nosupbnd1lem3
    syl112anc
    neneqd
    3jca
    mtand
    vx
    vy
    vv
    vu
    cA
    cS
    cU
    vg
    nosupbnd1.1
    nosupbnd1lem1
    @5
    @7
    csur
    wcel
    #
    cS
    csur
    wcel
    #
    @8
    @9
    @10
    w3o
    #
    @5
    @20
    @6
    con0
    wcel
    #
    @27
    @21
    @5
    @28
    @30
    @3
    @0
    @28
    @4
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
    nodmon
    syl
    cU
    @6
    noreson
    syl2anc
    @31
    csur
    cslt
    wor
    @27
    @28
    wa
    @29
    sltso
    csur
    @7
    cS
    cslt
    solin
    mpan
    syl2anc
    ecase23d
end
