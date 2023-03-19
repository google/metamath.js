include "cfn.mm"
include "wcel.mm"
include "cn.mm"
include "cz.mm"
include "wral.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "cmo.mm"
include "co.mm"
include "csu.mm"
include "cv.mm"
include "csb.mm"
include "cr.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
include "diffi.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "wi.mm"
include "eldifi.mm"
include "rspcsbela.mm"
include "sylan.mm"
include "expcom.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "cvv.mm"
include "wceq.mm"
include "vex.mm"
include "csbov1g.mm"
include "ax-mp.mm"
include "zre.mm"
include "adantl.mm"
include "crp.mm"
include "nnrp.mm"
include "adantr.mm"
include "modcld.mm"
include "syl5eqel.mm"
include "ex.mm"
include "3ad2ant2.mm"
include "mpd.mm"
include "fsumrecl.mm"

theorem fsummmodsndifre
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cN: class N
  let cX: class X
  let vx: setvar x

  disjoint A k
  disjoint X k
  disjoint N k
  disjoint A x
  disjoint k x
  disjoint B x
  disjoint X x
  disjoint N x
  disjoint k x
  assert |- ( ( A e. Fin /\ N e. NN /\ A. k e. A B e. ZZ ) -> sum_ k e. ( A \ { X } ) ( B mod N ) e. RR )

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
    wral
    #
    w3a
    #
    cA
    cX
    csn
    #
    cdif
    #
    cB
    cN
    cmo
    co
    #
    vk
    csu
    @5
    vk
    vx
    cv
    #
    @6
    csb
    #
    vx
    csu
    cr
    @5
    @6
    @8
    vk
    vx
    vx
    @6
    nfcv
    vk
    @7
    @6
    nfcsb1v
    vk
    @7
    @6
    csbeq1a
    cbvsumi
    @3
    @5
    @8
    vx
    @0
    @1
    @5
    cfn
    wcel
    @2
    cA
    @4
    diffi
    3ad2ant1
    @3
    @7
    @5
    wcel
    #
    wa
    vk
    @7
    cB
    csb
    #
    cz
    wcel
    #
    @8
    cr
    wcel
    #
    @3
    @9
    @11
    @2
    @0
    @9
    @11
    wi
    @1
    @9
    @2
    @11
    @9
    @7
    cA
    wcel
    @2
    @11
    @7
    cA
    @4
    eldifi
    vk
    @7
    cA
    cB
    cz
    rspcsbela
    sylan
    expcom
    3ad2ant3
    imp
    @3
    @11
    @12
    wi
    #
    @9
    @1
    @0
    @13
    @2
    @1
    @11
    @12
    @1
    @11
    wa
    #
    @8
    @10
    cN
    cmo
    co
    #
    cr
    @7
    cvv
    wcel
    @8
    @15
    wceq
    vx
    vex
    vk
    @7
    cB
    cN
    cmo
    cvv
    csbov1g
    ax-mp
    @14
    @10
    cN
    @11
    @10
    cr
    wcel
    @1
    @10
    zre
    adantl
    @1
    cN
    crp
    wcel
    @11
    cN
    nnrp
    adantr
    modcld
    syl5eqel
    ex
    3ad2ant2
    adantr
    mpd
    fsumrecl
    syl5eqel
end
