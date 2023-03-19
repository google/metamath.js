include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cusgr.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "w3a.mm"
include "cedg.mm"
include "cfn.mm"
include "c0.mm"
include "cuhgr.mm"
include "cvtx.mm"
include "usgruhgr.mm"
include "3ad2ant2.mm"
include "opvtxfv.mm"
include "3ad2ant1.mm"
include "wi.mm"
include "hasheq0.mm"
include "biimpd.mm"
include "adantr.mm"
include "a1d.mm"
include "3imp.mm"
include "eqtrd.mm"
include "eqid.mm"
include "uhgr0v0e.mm"
include "syl2anc.mm"
include "0fin.mm"
include "syl6eqel.mm"
include "ciedg.mm"
include "wb.mm"
include "usgredgffibi.mm"
include "opiedgfv.mm"
include "eleq1d.mm"
include "bitrd.mm"
include "mpbid.mm"

theorem fusgrfisbase
  let cE: class E
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( ( V e. X /\ E e. Y ) /\ <. V , E >. e. USGraph /\ ( # ` V ) = 0 ) -> E e. Fin )

  proof
    cV
    cX
    wcel
    #
    cE
    cY
    wcel
    #
    wa
    #
    cV
    cE
    cop
    #
    cusgr
    wcel
    #
    cV
    chash
    cfv
    cc0
    wceq
    #
    w3a
    #
    @3
    cedg
    cfv
    #
    cfn
    wcel
    #
    cE
    cfn
    wcel
    #
    @6
    @7
    c0
    cfn
    @6
    @3
    cuhgr
    wcel
    #
    @3
    cvtx
    cfv
    #
    c0
    wceq
    @7
    c0
    wceq
    @4
    @2
    @10
    @5
    @3
    usgruhgr
    3ad2ant2
    @6
    @11
    cV
    c0
    @2
    @4
    @11
    cV
    wceq
    @5
    cE
    cV
    cX
    cY
    opvtxfv
    3ad2ant1
    @2
    @4
    @5
    cV
    c0
    wceq
    #
    @2
    @5
    @12
    wi
    #
    @4
    @0
    @13
    @1
    @0
    @5
    @12
    cV
    cX
    hasheq0
    biimpd
    adantr
    a1d
    3imp
    eqtrd
    @7
    @3
    @11
    @11
    eqid
    @7
    eqid
    #
    uhgr0v0e
    syl2anc
    0fin
    syl6eqel
    @6
    @8
    @3
    ciedg
    cfv
    #
    cfn
    wcel
    #
    @9
    @4
    @2
    @8
    @16
    wb
    @5
    @7
    @3
    @15
    @15
    eqid
    @14
    usgredgffibi
    3ad2ant2
    @6
    @15
    cE
    cfn
    @2
    @4
    @15
    cE
    wceq
    @5
    cE
    cV
    cX
    cY
    opiedgfv
    3ad2ant1
    eleq1d
    bitrd
    mpbid
end
