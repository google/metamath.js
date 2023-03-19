include "cz.mm"
include "wcel.mm"
include "cc.mm"
include "caddc.mm"
include "co.mm"
include "wa.mm"
include "cmin.mm"
include "wceq.mm"
include "zcn.mm"
include "pncan.mm"
include "sylan2.mm"
include "ancoms.mm"
include "adantr.mm"
include "zsubcl.mm"
include "adantlr.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "wi.mm"
include "zaddcl.mm"
include "expcom.mm"
include "impbid.mm"
include "pm5.32da.mm"
include "pm4.71ri.mm"
include "syl6bbr.mm"

theorem zrevaddcl
  let cM: class M
  let cN: class N


  assert |- ( N e. ZZ -> ( ( M e. CC /\ ( M + N ) e. ZZ ) <-> M e. ZZ ) )

  proof
    cN
    cz
    wcel
    #
    cM
    cc
    wcel
    #
    cM
    cN
    caddc
    co
    #
    cz
    wcel
    #
    wa
    @1
    cM
    cz
    wcel
    #
    wa
    @4
    @0
    @1
    @3
    @4
    @0
    @1
    wa
    #
    @3
    @4
    @5
    @3
    @4
    @5
    @3
    wa
    @2
    cN
    cmin
    co
    #
    cM
    cz
    @5
    @6
    cM
    wceq
    #
    @3
    @1
    @0
    @7
    @0
    @1
    cN
    cc
    wcel
    @7
    cN
    zcn
    cM
    cN
    pncan
    sylan2
    ancoms
    adantr
    @0
    @3
    @6
    cz
    wcel
    #
    @1
    @3
    @0
    @8
    @2
    cN
    zsubcl
    ancoms
    adantlr
    eqeltrrd
    ex
    @0
    @4
    @3
    wi
    @1
    @4
    @0
    @3
    cM
    cN
    zaddcl
    expcom
    adantr
    impbid
    pm5.32da
    @4
    @1
    cM
    zcn
    pm4.71ri
    syl6bbr
end
