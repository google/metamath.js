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
include "simp3rr.mm"
include "con0.mm"
include "wi.mm"
include "simp2l.mm"
include "simp3rl.mm"
include "sseldd.mm"
include "simp3ll.mm"
include "nosupno.mm"
include "3ad2ant2.mm"
include "nodmon.mm"
include "syl.mm"
include "sltres.mm"
include "syl3anc.mm"
include "mtod.mm"
include "simp3lr.mm"
include "breq2d.mm"
include "mtbid.mm"
include "nosupbnd1lem1.mm"
include "syld3an3.mm"
include "wb.mm"
include "noreson.mm"
include "syl2anc.mm"
include "wor.mm"
include "sltso.mm"
include "sotrieq2.mm"
include "mpan.mm"
include "mpbir2and.mm"

theorem nosupbnd1lem2
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cU: class U
  let vg: setvar g
  let cW: class W
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
  disjoint W v
  disjoint x y
  assert |- ( ( -. E. x e. A A. y e. A -. x <s y /\ ( A C_ No /\ A e. _V ) /\ ( ( U e. A /\ ( U |` dom S ) = S ) /\ ( W e. A /\ -. W <s U ) ) ) -> ( W |` dom S ) = S )

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
    cW
    cA
    wcel
    #
    cW
    cU
    cslt
    wbr
    #
    wn
    #
    wa
    #
    wa
    #
    w3a
    #
    cW
    @5
    cres
    #
    cS
    wceq
    #
    @15
    cS
    cslt
    wbr
    #
    wn
    #
    cS
    @15
    cslt
    wbr
    wn
    #
    @14
    @15
    @6
    cslt
    wbr
    #
    @17
    @14
    @20
    @10
    @9
    @11
    @8
    @0
    @3
    simp3rr
    @14
    cW
    csur
    wcel
    #
    cU
    csur
    wcel
    @5
    con0
    wcel
    #
    @20
    @10
    wi
    @14
    cA
    csur
    cW
    @0
    @1
    @2
    @13
    simp2l
    #
    @9
    @11
    @8
    @0
    @3
    simp3rl
    #
    sseldd
    #
    @14
    cA
    csur
    cU
    @23
    @4
    @7
    @12
    @0
    @3
    simp3ll
    sseldd
    @14
    cS
    csur
    wcel
    #
    @22
    @3
    @0
    @26
    @13
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
    #
    cW
    cU
    @5
    sltres
    syl3anc
    mtod
    @14
    @6
    cS
    @15
    cslt
    @4
    @7
    @12
    @0
    @3
    simp3lr
    breq2d
    mtbid
    @0
    @3
    @13
    @9
    @19
    @24
    vx
    vy
    vv
    vu
    cA
    cS
    cW
    vg
    nosupbnd1.1
    nosupbnd1lem1
    syld3an3
    @14
    @15
    csur
    wcel
    #
    @26
    @16
    @18
    @19
    wa
    wb
    #
    @14
    @21
    @22
    @29
    @25
    @28
    cW
    @5
    noreson
    syl2anc
    @27
    csur
    cslt
    wor
    @29
    @26
    wa
    @30
    sltso
    csur
    @15
    cS
    cslt
    sotrieq2
    mpan
    syl2anc
    mpbir2and
end
