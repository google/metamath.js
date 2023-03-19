include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "wnel.mm"
include "cz.mm"
include "csn.mm"
include "cun.mm"
include "wral.mm"
include "w3a.mm"
include "csu.mm"
include "caddc.mm"
include "co.mm"
include "csb.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "df-nel.mm"
include "disjsn.mm"
include "sylbb2.mm"
include "3ad2ant2.mm"
include "eqidd.mm"
include "snfi.mm"
include "unfi.mm"
include "mpan2.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "wi.mm"
include "rspcsbela.mm"
include "expcom.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "zcnd.mm"
include "fsumsplit.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
include "oveq12i.mm"
include "3eqtr4g.mm"
include "cvv.mm"
include "cc.mm"
include "vex.mm"
include "vsnid.mm"
include "elun2.mm"
include "ax-mp.mm"
include "mpan.mm"
include "sumsns.mm"
include "sylancr.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem fsumsplitsnunOLD
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x

  disjoint A k
  disjoint k z
  disjoint A x
  disjoint k x
  disjoint B x
  disjoint x z
  assert |- ( ( A e. Fin /\ z e/ A /\ A. k e. ( A u. { z } ) B e. ZZ ) -> sum_ k e. ( A u. { z } ) B = ( sum_ k e. A B + [_ z / k ]_ B ) )

  proof
    cA
    cfn
    wcel
    #
    vz
    cv
    #
    cA
    wnel
    #
    cB
    cz
    wcel
    vk
    cA
    @1
    csn
    #
    cun
    #
    wral
    #
    w3a
    #
    @4
    cB
    vk
    csu
    #
    cA
    cB
    vk
    csu
    #
    @3
    cB
    vk
    csu
    #
    caddc
    co
    #
    @8
    vk
    @1
    cB
    csb
    #
    caddc
    co
    @6
    @4
    vk
    vx
    cv
    #
    cB
    csb
    #
    vx
    csu
    cA
    @13
    vx
    csu
    #
    @3
    @13
    vx
    csu
    #
    caddc
    co
    @7
    @10
    @6
    cA
    @3
    @13
    @4
    vx
    @2
    @0
    cA
    @3
    cin
    c0
    wceq
    #
    @5
    @2
    @1
    cA
    wcel
    wn
    @16
    @1
    cA
    df-nel
    cA
    @1
    disjsn
    sylbb2
    3ad2ant2
    @6
    @4
    eqidd
    @0
    @2
    @4
    cfn
    wcel
    #
    @5
    @0
    @3
    cfn
    wcel
    @17
    @1
    snfi
    cA
    @3
    unfi
    mpan2
    3ad2ant1
    @6
    @12
    @4
    wcel
    #
    wa
    @13
    @6
    @18
    @13
    cz
    wcel
    #
    @5
    @0
    @18
    @19
    wi
    @2
    @18
    @5
    @19
    vk
    @12
    @4
    cB
    cz
    rspcsbela
    expcom
    3ad2ant3
    imp
    zcnd
    fsumsplit
    @4
    cB
    @13
    vk
    vx
    vx
    cB
    nfcv
    #
    vk
    @12
    cB
    nfcsb1v
    #
    vk
    @12
    cB
    csbeq1a
    #
    cbvsumi
    @8
    @14
    @9
    @15
    caddc
    cA
    cB
    @13
    vk
    vx
    @20
    @21
    @22
    cbvsumi
    @3
    cB
    @13
    vk
    vx
    @20
    @21
    @22
    cbvsumi
    oveq12i
    3eqtr4g
    @6
    @9
    @11
    @8
    caddc
    @6
    @1
    cvv
    wcel
    @11
    cc
    wcel
    #
    @9
    @11
    wceq
    vz
    vex
    @5
    @0
    @23
    @2
    @5
    @11
    @1
    @4
    wcel
    #
    @5
    @11
    cz
    wcel
    @1
    @3
    wcel
    @24
    vz
    vsnid
    @1
    @3
    cA
    elun2
    ax-mp
    vk
    @1
    @4
    cB
    cz
    rspcsbela
    mpan
    zcnd
    3ad2ant3
    cB
    vk
    @1
    cvv
    sumsns
    sylancr
    oveq2d
    eqtrd
end
