include "cupgr.mm"
include "wcel.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wceq.mm"
include "nbgrval.mm"
include "adantl.mm"
include "cvv.mm"
include "wne.mm"
include "w3a.mm"
include "simp-4l.mm"
include "simpr.mm"
include "adantr.mm"
include "vex.mm"
include "a1i.mm"
include "eldifsn.mm"
include "necomd.mm"
include "sylbi.mm"
include "3jca.mm"
include "upgredgpr.mm"
include "syl31anc.mm"
include "ex.mm"
include "eleq1.mm"
include "biimprd.mm"
include "syl6ci.mm"
include "rexlimdva.mm"
include "wb.mm"
include "sseq2.mm"
include "ssid.mm"
include "rspcedvd.mm"
include "impbid.mm"
include "rabbidva.mm"
include "eqtrd.mm"

theorem nbupgr
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let ve: setvar e
  let cX: class X
  let vv: setvar v
  let vx: setvar x
  assume nbuhgr.v: |- V = ( Vtx ` G )
  assume nbuhgr.e: |- E = ( Edg ` G )

  disjoint G n
  disjoint N n
  disjoint V n
  disjoint E n
  disjoint E e
  disjoint G e
  disjoint e n
  disjoint N e
  disjoint V e
  disjoint X e
  disjoint X n
  disjoint E v
  disjoint E x
  disjoint n v
  disjoint n x
  disjoint v x
  disjoint G x
  disjoint e x
  disjoint G v
  disjoint N v
  disjoint N x
  disjoint V v
  disjoint V x
  assert |- ( ( G e. UPGraph /\ N e. V ) -> ( G NeighbVtx N ) = { n e. ( V \ { N } ) | { N , n } e. E } )

  proof
    cG
    cupgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    cG
    cN
    cnbgr
    co
    #
    cN
    vn
    cv
    #
    cpr
    #
    ve
    cv
    #
    wss
    #
    ve
    cE
    wrex
    #
    vn
    cV
    cN
    csn
    cdif
    #
    crab
    #
    @5
    cE
    wcel
    #
    vn
    @9
    crab
    @1
    @3
    @10
    wceq
    @0
    ve
    vn
    cE
    cG
    cN
    cV
    nbuhgr.v
    nbuhgr.e
    nbgrval
    adantl
    @2
    @8
    @11
    vn
    @9
    @2
    @4
    @9
    wcel
    #
    wa
    #
    @8
    @11
    @13
    @7
    @11
    ve
    cE
    @13
    @6
    cE
    wcel
    #
    wa
    #
    @7
    @5
    @6
    wceq
    #
    @14
    @11
    @15
    @7
    @16
    @15
    @7
    wa
    @0
    @14
    @7
    @1
    @4
    cvv
    wcel
    #
    cN
    @4
    wne
    #
    w3a
    #
    @16
    @0
    @1
    @12
    @14
    @7
    simp-4l
    @15
    @14
    @7
    @13
    @14
    simpr
    #
    adantr
    @15
    @7
    simpr
    @15
    @19
    @7
    @13
    @19
    @14
    @13
    @1
    @17
    @18
    @2
    @1
    @12
    @0
    @1
    simpr
    adantr
    @17
    @13
    vn
    vex
    a1i
    @12
    @18
    @2
    @12
    @4
    cV
    wcel
    #
    @4
    cN
    wne
    #
    wa
    #
    @18
    @4
    cV
    cN
    eldifsn
    @23
    @4
    cN
    @21
    @22
    simpr
    necomd
    sylbi
    adantl
    3jca
    adantr
    adantr
    cN
    @4
    @6
    cV
    cE
    cG
    cV
    cvv
    nbuhgr.v
    nbuhgr.e
    upgredgpr
    syl31anc
    ex
    @20
    @16
    @11
    @14
    @5
    @6
    cE
    eleq1
    biimprd
    syl6ci
    rexlimdva
    @13
    @11
    @8
    @13
    @11
    wa
    #
    @7
    @5
    @5
    wss
    #
    ve
    @5
    cE
    @13
    @11
    simpr
    @6
    @5
    wceq
    @7
    @25
    wb
    @24
    @6
    @5
    @5
    sseq2
    adantl
    @25
    @24
    @5
    ssid
    a1i
    rspcedvd
    ex
    impbid
    rabbidva
    eqtrd
end
