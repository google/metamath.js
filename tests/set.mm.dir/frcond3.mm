include "cfrgr.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cnbgr.mm"
include "co.mm"
include "cin.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cpr.mm"
include "wss.mm"
include "wreu.mm"
include "frcond1.mm"
include "imp.mm"
include "crab.mm"
include "wex.mm"
include "ssrab2.mm"
include "sseq1.mm"
include "mpbii.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "adantl.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "nbusgr.mm"
include "ineq12d.mm"
include "syl.mm"
include "adantr.mm"
include "inrab.mm"
include "syl6eq.mm"
include "wb.mm"
include "prcom.mm"
include "eleq1i.mm"
include "anbi2i.mm"
include "prex.mm"
include "prss.mm"
include "bitri.mm"
include "a1i.mm"
include "rabbidva.mm"
include "simpr.mm"
include "3eqtrd.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "reusn.mm"
include "df-rex.mm"
include "3imtr4g.mm"
include "mpd.mm"

theorem frcond3
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let vb: setvar b
  let vk: setvar k
  let vl: setvar l
  assume frcond1.v: |- V = ( Vtx ` G )
  assume frcond1.e: |- E = ( Edg ` G )

  disjoint A x
  disjoint C x
  disjoint E x
  disjoint G x
  disjoint V x
  disjoint A b
  disjoint A k
  disjoint A l
  disjoint b k
  disjoint b l
  disjoint k l
  disjoint C b
  disjoint C k
  disjoint C l
  disjoint E k
  disjoint E l
  disjoint G b
  disjoint G k
  disjoint G l
  disjoint V b
  disjoint V k
  disjoint V l
  disjoint E b
  disjoint b x
  assert |- ( G e. FriendGraph -> ( ( A e. V /\ C e. V /\ A =/= C ) -> E. x e. V ( ( G NeighbVtx A ) i^i ( G NeighbVtx C ) ) = { x } ) )

  proof
    cG
    cfrgr
    wcel
    #
    cA
    cV
    wcel
    cC
    cV
    wcel
    cA
    cC
    wne
    w3a
    #
    cG
    cA
    cnbgr
    co
    #
    cG
    cC
    cnbgr
    co
    #
    cin
    #
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    cV
    wrex
    #
    @0
    @1
    wa
    #
    cA
    vb
    cv
    #
    cpr
    #
    @10
    cC
    cpr
    #
    cpr
    cE
    wss
    #
    vb
    cV
    wreu
    #
    @8
    @0
    @1
    @14
    cA
    cC
    cE
    cG
    cV
    vb
    frcond1.v
    frcond1.e
    frcond1
    imp
    @9
    @13
    vb
    cV
    crab
    #
    @6
    wceq
    #
    vx
    wex
    @5
    cV
    wcel
    #
    @7
    wa
    #
    vx
    wex
    @14
    @8
    @9
    @16
    @18
    vx
    @9
    @16
    @18
    @9
    @16
    wa
    #
    @17
    @7
    @16
    @17
    @9
    @16
    @6
    cV
    wss
    #
    @17
    @16
    @15
    cV
    wss
    @20
    @13
    vb
    cV
    ssrab2
    @15
    @6
    cV
    sseq1
    mpbii
    @5
    cV
    vx
    vex
    snss
    sylibr
    adantl
    @19
    @4
    @11
    cE
    wcel
    #
    cC
    @10
    cpr
    #
    cE
    wcel
    #
    wa
    #
    vb
    cV
    crab
    #
    @15
    @6
    @19
    @4
    @21
    vb
    cV
    crab
    #
    @23
    vb
    cV
    crab
    #
    cin
    #
    @25
    @9
    @4
    @28
    wceq
    #
    @16
    @0
    @29
    @1
    @0
    cG
    cusgr
    wcel
    #
    @29
    cG
    frgrusgr
    @30
    @2
    @26
    @3
    @27
    vb
    cE
    cG
    cA
    cV
    frcond1.v
    frcond1.e
    nbusgr
    vb
    cE
    cG
    cC
    cV
    frcond1.v
    frcond1.e
    nbusgr
    ineq12d
    syl
    adantr
    adantr
    @21
    @23
    vb
    cV
    inrab
    syl6eq
    @9
    @25
    @15
    wceq
    @16
    @9
    @24
    @13
    vb
    cV
    @24
    @13
    wb
    @9
    @10
    cV
    wcel
    wa
    @24
    @21
    @12
    cE
    wcel
    #
    wa
    @13
    @23
    @31
    @21
    @22
    @12
    cE
    cC
    @10
    prcom
    eleq1i
    anbi2i
    @11
    @12
    cE
    cA
    @10
    prex
    @10
    cC
    prex
    prss
    bitri
    a1i
    rabbidva
    adantr
    @9
    @16
    simpr
    3eqtrd
    jca
    ex
    eximdv
    @13
    vb
    vx
    cV
    reusn
    @7
    vx
    cV
    df-rex
    3imtr4g
    mpd
    ex
end
