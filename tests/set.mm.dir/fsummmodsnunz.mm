include "cfn.mm"
include "wcel.mm"
include "cn.mm"
include "cz.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "wral.mm"
include "w3a.mm"
include "cmo.mm"
include "co.mm"
include "csu.mm"
include "csb.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
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
include "cvv.mm"
include "wceq.mm"
include "vex.mm"
include "csbov1g.mm"
include "ax-mp.mm"
include "simpr.mm"
include "simpl.mm"
include "zmodcld.mm"
include "nn0zd.mm"
include "syl5eqel.mm"
include "ex.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "mpd.mm"
include "fsumzcl.mm"

theorem fsummmodsnunz
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cN: class N
  let vx: setvar x

  disjoint A k
  disjoint N k
  disjoint k z
  disjoint A x
  disjoint k x
  disjoint B x
  disjoint N x
  disjoint x z
  disjoint k x
  assert |- ( ( A e. Fin /\ N e. NN /\ A. k e. ( A u. { z } ) B e. ZZ ) -> sum_ k e. ( A u. { z } ) ( B mod N ) e. ZZ )

  proof
    cA
    cfn
    wcel
    #
    cN
    cn
    wcel
    #
    cB
    cz
    wcel
    vk
    cA
    vz
    cv
    #
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
    cN
    cmo
    co
    #
    vk
    csu
    @4
    vk
    vx
    cv
    #
    @7
    csb
    #
    vx
    csu
    cz
    @4
    @7
    @9
    vk
    vx
    vx
    @7
    nfcv
    vk
    @8
    @7
    nfcsb1v
    vk
    @8
    @7
    csbeq1a
    cbvsumi
    @6
    @4
    @9
    vx
    @0
    @1
    @4
    cfn
    wcel
    #
    @5
    @0
    @3
    cfn
    wcel
    @10
    @2
    snfi
    cA
    @3
    unfi
    mpan2
    3ad2ant1
    @6
    @8
    @4
    wcel
    #
    wa
    vk
    @8
    cB
    csb
    #
    cz
    wcel
    #
    @9
    cz
    wcel
    #
    @6
    @11
    @13
    @5
    @0
    @11
    @13
    wi
    @1
    @11
    @5
    @13
    vk
    @8
    @4
    cB
    cz
    rspcsbela
    expcom
    3ad2ant3
    imp
    @6
    @13
    @14
    wi
    #
    @11
    @1
    @0
    @15
    @5
    @1
    @13
    @14
    @1
    @13
    wa
    #
    @9
    @12
    cN
    cmo
    co
    #
    cz
    @8
    cvv
    wcel
    @9
    @17
    wceq
    vx
    vex
    vk
    @8
    cB
    cN
    cmo
    cvv
    csbov1g
    ax-mp
    @16
    @17
    @16
    @12
    cN
    @1
    @13
    simpr
    @1
    @13
    simpl
    zmodcld
    nn0zd
    syl5eqel
    ex
    3ad2ant2
    adantr
    mpd
    fsumzcl
    syl5eqel
end
