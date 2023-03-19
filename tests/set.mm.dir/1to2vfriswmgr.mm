include "csn.mm"
include "wceq.mm"
include "cpr.mm"
include "wo.mm"
include "wcel.mm"
include "cfrgr.mm"
include "cv.mm"
include "cdif.mm"
include "wreu.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "1vwmgr.mm"
include "a1d.mm"
include "expcom.mm"
include "cvv.mm"
include "wne.mm"
include "wnel.mm"
include "wn.mm"
include "w3a.mm"
include "cvtx.mm"
include "cfv.mm"
include "simpr.mm"
include "simpll.mm"
include "simplr.mm"
include "3jca.mm"
include "eqeq1i.mm"
include "biimpi.mm"
include "nfrgr2v.mm"
include "syl2anr.mm"
include "df-nel.mm"
include "sylib.mm"
include "pm2.21d.mm"
include "ex.mm"
include "com23.mm"
include "ianor.mm"
include "prprc2.mm"
include "nne.mm"
include "preq2.mm"
include "eqcoms.mm"
include "dfsn2.mm"
include "syl6eqr.mm"
include "sylbi.mm"
include "jaoi.mm"
include "eqeq2d.mm"
include "syl6bi.mm"
include "pm2.61i.mm"
include "impcom.mm"

theorem 1to2vfriswmgr
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let vh: setvar h
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let vy: setvar y
  let cC: class C
  let cY: class Y
  assume 3vfriswmgr.v: |- V = ( Vtx ` G )
  assume 3vfriswmgr.e: |- E = ( Edg ` G )

  disjoint A w
  disjoint B w
  disjoint E w
  disjoint G w
  disjoint V w
  disjoint X w
  disjoint A h
  disjoint A v
  disjoint h v
  disjoint h w
  disjoint v w
  disjoint B h
  disjoint B v
  disjoint E h
  disjoint E v
  disjoint V h
  disjoint V v
  disjoint A y
  disjoint w y
  disjoint B y
  disjoint C w
  disjoint C y
  disjoint E y
  disjoint G y
  disjoint V y
  disjoint X y
  disjoint Y w
  disjoint Y y
  disjoint C h
  disjoint C v
  assert |- ( ( A e. X /\ ( V = { A } \/ V = { A , B } ) ) -> ( G e. FriendGraph -> E. h e. V A. v e. ( V \ { h } ) ( { v , h } e. E /\ E! w e. ( V \ { h } ) { v , w } e. E ) ) )

  proof
    cV
    cA
    csn
    #
    wceq
    #
    cV
    cA
    cB
    cpr
    #
    wceq
    #
    wo
    cA
    cX
    wcel
    #
    cG
    cfrgr
    wcel
    #
    vv
    cv
    #
    vh
    cv
    #
    cpr
    cE
    wcel
    @6
    vw
    cv
    cpr
    cE
    wcel
    vw
    cV
    @7
    csn
    cdif
    #
    wreu
    wa
    vv
    @8
    wral
    vh
    cV
    wrex
    #
    wi
    #
    @1
    @4
    @10
    wi
    #
    @3
    @4
    @1
    @10
    @4
    @1
    wa
    @9
    @5
    vw
    vv
    cA
    vh
    cE
    cV
    cX
    1vwmgr
    a1d
    expcom
    #
    cB
    cvv
    wcel
    #
    cA
    cB
    wne
    #
    wa
    #
    @3
    @11
    wi
    @15
    @4
    @3
    @10
    @15
    @4
    @3
    @10
    wi
    @3
    @15
    @4
    wa
    #
    @10
    @3
    @16
    wa
    #
    @5
    @9
    @17
    cG
    cfrgr
    wnel
    #
    @5
    wn
    @16
    @4
    @13
    @14
    w3a
    cG
    cvtx
    cfv
    #
    @2
    wceq
    #
    @18
    @3
    @16
    @4
    @13
    @14
    @15
    @4
    simpr
    @13
    @14
    @4
    simpll
    @13
    @14
    @4
    simplr
    3jca
    @3
    @20
    cV
    @19
    @2
    3vfriswmgr.v
    eqeq1i
    biimpi
    cA
    cB
    cG
    cX
    cvv
    nfrgr2v
    syl2anr
    cG
    cfrgr
    df-nel
    sylib
    pm2.21d
    expcom
    ex
    com23
    @15
    wn
    #
    @3
    @1
    @11
    @21
    @2
    @0
    cV
    @21
    @13
    wn
    #
    @14
    wn
    #
    wo
    @2
    @0
    wceq
    #
    @13
    @14
    ianor
    @22
    @24
    @23
    cA
    cB
    prprc2
    @23
    cA
    cB
    wceq
    #
    @24
    cA
    cB
    nne
    @25
    @2
    cA
    cA
    cpr
    #
    @0
    @2
    @26
    wceq
    cB
    cA
    cB
    cA
    cA
    preq2
    eqcoms
    cA
    dfsn2
    syl6eqr
    sylbi
    jaoi
    sylbi
    eqeq2d
    @12
    syl6bi
    pm2.61i
    jaoi
    impcom
end
