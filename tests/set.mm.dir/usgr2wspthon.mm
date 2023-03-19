include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cwwspthsnon.mm"
include "co.mm"
include "cv.mm"
include "cs3.mm"
include "wceq.mm"
include "wrex.mm"
include "wne.mm"
include "cpr.mm"
include "cupgr.mm"
include "wb.mm"
include "usgrupgr.mm"
include "adantr.mm"
include "simpl.mm"
include "adantl.mm"
include "simpr.mm"
include "elwspths2on.mm"
include "syl3anc.mm"
include "w3a.mm"
include "simplrl.mm"
include "simplrr.mm"
include "usgr2wspthons3.mm"
include "syl13anc.mm"
include "anbi2d.mm"
include "anass.mm"
include "3anass.mm"
include "bicomi.mm"
include "anbi2i.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "rexbidva.mm"
include "bitrd.mm"

theorem usgr2wspthon
  let cA: class A
  let cC: class C
  let cT: class T
  let cE: class E
  let cG: class G
  let cV: class V
  let vb: setvar b
  assume usgr2wspthon0.v: |- V = ( Vtx ` G )
  assume usgr2wspthon0.e: |- E = ( Edg ` G )

  disjoint A b
  disjoint C b
  disjoint G b
  disjoint V b
  disjoint T b
  assert |- ( ( G e. USGraph /\ ( A e. V /\ C e. V ) ) -> ( T e. ( A ( 2 WSPathsNOn G ) C ) <-> E. b e. V ( ( T = <" A b C "> /\ A =/= C ) /\ ( { A , b } e. E /\ { b , C } e. E ) ) ) )

  proof
    cG
    cusgr
    wcel
    #
    cA
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    wa
    #
    wa
    #
    cT
    cA
    cC
    c2
    cG
    cwwspthsnon
    co
    co
    #
    wcel
    #
    cT
    cA
    vb
    cv
    #
    cC
    cs3
    #
    wceq
    #
    @8
    @5
    wcel
    #
    wa
    #
    vb
    cV
    wrex
    #
    @9
    cA
    cC
    wne
    #
    wa
    cA
    @7
    cpr
    cE
    wcel
    #
    @7
    cC
    cpr
    cE
    wcel
    #
    wa
    #
    wa
    #
    vb
    cV
    wrex
    @4
    cG
    cupgr
    wcel
    #
    @1
    @2
    @6
    @12
    wb
    @0
    @18
    @3
    cG
    usgrupgr
    adantr
    @3
    @1
    @0
    @1
    @2
    simpl
    adantl
    @3
    @2
    @0
    @1
    @2
    simpr
    adantl
    cA
    cC
    cG
    cV
    cT
    vb
    usgr2wspthon0.v
    elwspths2on
    syl3anc
    @4
    @11
    @17
    vb
    cV
    @4
    @7
    cV
    wcel
    #
    wa
    #
    @11
    @9
    @13
    @14
    @15
    w3a
    #
    wa
    #
    @17
    @20
    @10
    @21
    @9
    @20
    @0
    @1
    @19
    @2
    @10
    @21
    wb
    @4
    @0
    @19
    @0
    @3
    simpl
    adantr
    @0
    @1
    @2
    @19
    simplrl
    @4
    @19
    simpr
    @0
    @1
    @2
    @19
    simplrr
    cA
    @7
    cC
    cE
    cG
    cV
    usgr2wspthon0.v
    usgr2wspthon0.e
    usgr2wspthons3
    syl13anc
    anbi2d
    @17
    @9
    @13
    @16
    wa
    #
    wa
    @22
    @9
    @13
    @16
    anass
    @23
    @21
    @9
    @21
    @23
    @13
    @14
    @15
    3anass
    bicomi
    anbi2i
    bitri
    syl6bbr
    rexbidva
    bitrd
end
