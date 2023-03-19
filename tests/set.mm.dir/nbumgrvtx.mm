include "cumgr.mm"
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
include "eldifi.mm"
include "adantr.mm"
include "cupgr.mm"
include "cvv.mm"
include "wne.mm"
include "w3a.mm"
include "umgrupgr.mm"
include "ad4antr.mm"
include "simpr.mm"
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
include "impr.mm"
include "jca.mm"
include "rexlimdvaa.mm"
include "expimpd.mm"
include "simprl.mm"
include "umgredgne.mm"
include "ad2ant2rl.mm"
include "sylanbrc.mm"
include "wb.mm"
include "sseq2.mm"
include "ssid.mm"
include "rspcedvd.mm"
include "impbid.mm"
include "preq2.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "eleq1d.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "eqtrd.mm"

theorem nbumgrvtx
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let ve: setvar e
  let cX: class X
  let vv: setvar v
  let vx: setvar x
  let cK: class K
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
  disjoint K n
  disjoint e v
  assert |- ( ( G e. UMGraph /\ N e. V ) -> ( G NeighbVtx N ) = { n e. V | { N , n } e. E } )

  proof
    cG
    cumgr
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
    vv
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
    vv
    cV
    cN
    csn
    #
    cdif
    #
    crab
    #
    cN
    vn
    cv
    #
    cpr
    #
    cE
    wcel
    #
    vn
    cV
    crab
    #
    @1
    @3
    @11
    wceq
    @0
    ve
    vv
    cE
    cG
    cN
    cV
    nbuhgr.v
    nbuhgr.e
    nbgrval
    adantl
    @2
    vx
    @11
    @15
    @2
    vx
    cv
    #
    @10
    wcel
    #
    cN
    @16
    cpr
    #
    @6
    wss
    #
    ve
    cE
    wrex
    #
    wa
    #
    @16
    cV
    wcel
    #
    @18
    cE
    wcel
    #
    wa
    #
    @16
    @11
    wcel
    @16
    @15
    wcel
    @2
    @21
    @24
    @2
    @17
    @20
    @24
    @2
    @17
    wa
    #
    @19
    @24
    ve
    cE
    @25
    @6
    cE
    wcel
    #
    @19
    wa
    #
    wa
    @22
    @23
    @25
    @22
    @27
    @17
    @22
    @2
    @16
    cV
    @9
    eldifi
    adantl
    adantr
    @25
    @26
    @19
    @23
    @25
    @26
    wa
    #
    @19
    @18
    @6
    wceq
    #
    @26
    @23
    @28
    @19
    @29
    @28
    @19
    wa
    cG
    cupgr
    wcel
    #
    @26
    @19
    @1
    @16
    cvv
    wcel
    #
    cN
    @16
    wne
    #
    w3a
    #
    @29
    @0
    @30
    @1
    @17
    @26
    @19
    cG
    umgrupgr
    ad4antr
    @28
    @26
    @19
    @25
    @26
    simpr
    #
    adantr
    @28
    @19
    simpr
    @28
    @33
    @19
    @25
    @33
    @26
    @25
    @1
    @31
    @32
    @2
    @1
    @17
    @0
    @1
    simpr
    adantr
    @31
    @25
    vx
    vex
    a1i
    @17
    @32
    @2
    @17
    @22
    @16
    cN
    wne
    #
    wa
    #
    @32
    @16
    cV
    cN
    eldifsn
    #
    @36
    @16
    cN
    @22
    @35
    simpr
    necomd
    sylbi
    adantl
    3jca
    adantr
    adantr
    cN
    @16
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
    @34
    @29
    @23
    @26
    @18
    @6
    cE
    eleq1
    biimprd
    syl6ci
    impr
    jca
    rexlimdvaa
    expimpd
    @2
    @24
    @21
    @2
    @24
    wa
    #
    @17
    @20
    @38
    @22
    @35
    @17
    @2
    @22
    @23
    simprl
    @38
    cN
    @16
    @0
    @23
    @32
    @1
    @22
    cE
    cG
    cN
    @16
    nbuhgr.e
    umgredgne
    ad2ant2rl
    necomd
    @37
    sylanbrc
    @38
    @19
    @18
    @18
    wss
    #
    ve
    @18
    cE
    @24
    @23
    @2
    @22
    @23
    simpr
    adantl
    @6
    @18
    wceq
    @19
    @39
    wb
    @38
    @6
    @18
    @18
    sseq2
    adantl
    @39
    @38
    @18
    ssid
    a1i
    rspcedvd
    jca
    ex
    impbid
    @8
    @20
    vv
    @16
    @10
    @4
    @16
    wceq
    #
    @7
    @19
    ve
    cE
    @40
    @5
    @18
    @6
    @4
    @16
    cN
    preq2
    sseq1d
    rexbidv
    elrab
    @14
    @23
    vn
    @16
    cV
    @12
    @16
    wceq
    @13
    @18
    cE
    @12
    @16
    cN
    preq2
    eleq1d
    elrab
    3bitr4g
    eqrdv
    eqtrd
end
