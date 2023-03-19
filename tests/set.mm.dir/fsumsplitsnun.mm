include "cfn.mm"
include "wcel.mm"
include "wnel.mm"
include "wa.mm"
include "cz.mm"
include "csn.mm"
include "cun.mm"
include "wral.mm"
include "w3a.mm"
include "csu.mm"
include "caddc.mm"
include "co.mm"
include "csb.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "df-nel.mm"
include "disjsn.mm"
include "sylbb2.mm"
include "adantl.mm"
include "3ad2ant2.mm"
include "eqidd.mm"
include "snfi.mm"
include "unfi.mm"
include "mpan2.mm"
include "3ad2ant1.mm"
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
include "cc.mm"
include "simp2l.mm"
include "snidg.mm"
include "adantr.mm"
include "elun2.mm"
include "syl.mm"
include "simp3.mm"
include "syl2anc.mm"
include "sumsns.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem fsumsplitsnun
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  let cZ: class Z
  let vx: setvar x

  disjoint A k
  disjoint Z k
  disjoint A x
  disjoint k x
  disjoint B x
  disjoint Z x
  disjoint V x
  assert |- ( ( A e. Fin /\ ( Z e. V /\ Z e/ A ) /\ A. k e. ( A u. { Z } ) B e. ZZ ) -> sum_ k e. ( A u. { Z } ) B = ( sum_ k e. A B + [_ Z / k ]_ B ) )

  proof
    cA
    cfn
    wcel
    #
    cZ
    cV
    wcel
    #
    cZ
    cA
    wnel
    #
    wa
    #
    cB
    cz
    wcel
    vk
    cA
    cZ
    csn
    #
    cun
    #
    wral
    #
    w3a
    #
    @5
    cB
    vk
    csu
    #
    cA
    cB
    vk
    csu
    #
    @4
    cB
    vk
    csu
    #
    caddc
    co
    #
    @9
    vk
    cZ
    cB
    csb
    #
    caddc
    co
    @7
    @5
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
    @14
    vx
    csu
    #
    @4
    @14
    vx
    csu
    #
    caddc
    co
    @8
    @11
    @7
    cA
    @4
    @14
    @5
    vx
    @3
    @0
    cA
    @4
    cin
    c0
    wceq
    #
    @6
    @2
    @17
    @1
    @2
    cZ
    cA
    wcel
    wn
    @17
    cZ
    cA
    df-nel
    cA
    cZ
    disjsn
    sylbb2
    adantl
    3ad2ant2
    @7
    @5
    eqidd
    @0
    @3
    @5
    cfn
    wcel
    #
    @6
    @0
    @4
    cfn
    wcel
    @18
    cZ
    snfi
    cA
    @4
    unfi
    mpan2
    3ad2ant1
    @7
    @13
    @5
    wcel
    #
    wa
    @14
    @7
    @19
    @14
    cz
    wcel
    #
    @6
    @0
    @19
    @20
    wi
    @3
    @19
    @6
    @20
    vk
    @13
    @5
    cB
    cz
    rspcsbela
    expcom
    3ad2ant3
    imp
    zcnd
    fsumsplit
    @5
    cB
    @14
    vk
    vx
    vx
    cB
    nfcv
    #
    vk
    @13
    cB
    nfcsb1v
    #
    vk
    @13
    cB
    csbeq1a
    #
    cbvsumi
    @9
    @15
    @10
    @16
    caddc
    cA
    cB
    @14
    vk
    vx
    @21
    @22
    @23
    cbvsumi
    @4
    cB
    @14
    vk
    vx
    @21
    @22
    @23
    cbvsumi
    oveq12i
    3eqtr4g
    @7
    @10
    @12
    @9
    caddc
    @7
    @1
    @12
    cc
    wcel
    @10
    @12
    wceq
    @0
    @1
    @2
    @6
    simp2l
    @7
    @12
    @7
    cZ
    @5
    wcel
    #
    @6
    @12
    cz
    wcel
    @7
    cZ
    @4
    wcel
    #
    @24
    @3
    @0
    @25
    @6
    @1
    @25
    @2
    cZ
    cV
    snidg
    adantr
    3ad2ant2
    cZ
    @4
    cA
    elun2
    syl
    @0
    @3
    @6
    simp3
    vk
    cZ
    @5
    cB
    cz
    rspcsbela
    syl2anc
    zcnd
    cB
    vk
    cZ
    cV
    sumsns
    syl2anc
    oveq2d
    eqtrd
end
