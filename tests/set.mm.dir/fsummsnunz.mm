include "cfn.mm"
include "wcel.mm"
include "cz.mm"
include "csn.mm"
include "cun.mm"
include "wral.mm"
include "wa.mm"
include "csu.mm"
include "cv.mm"
include "csb.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
include "snfi.mm"
include "a1i.mm"
include "unfi.mm"
include "syldan.mm"
include "wi.mm"
include "rspcsbela.mm"
include "expcom.mm"
include "adantl.mm"
include "imp.mm"
include "fsumzcl.mm"
include "syl5eqel.mm"

theorem fsummsnunz
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cZ: class Z
  let vx: setvar x

  disjoint A k
  disjoint Z k
  disjoint A x
  disjoint k x
  disjoint B x
  disjoint Z x
  assert |- ( ( A e. Fin /\ A. k e. ( A u. { Z } ) B e. ZZ ) -> sum_ k e. ( A u. { Z } ) B e. ZZ )

  proof
    cA
    cfn
    wcel
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
    wa
    #
    @2
    cB
    vk
    csu
    @2
    vk
    vx
    cv
    #
    cB
    csb
    #
    vx
    csu
    cz
    @2
    cB
    @6
    vk
    vx
    vx
    cB
    nfcv
    vk
    @5
    cB
    nfcsb1v
    vk
    @5
    cB
    csbeq1a
    cbvsumi
    @4
    @2
    @6
    vx
    @0
    @3
    @1
    cfn
    wcel
    #
    @2
    cfn
    wcel
    @7
    @4
    cZ
    snfi
    a1i
    cA
    @1
    unfi
    syldan
    @4
    @5
    @2
    wcel
    #
    @6
    cz
    wcel
    #
    @3
    @8
    @9
    wi
    @0
    @8
    @3
    @9
    vk
    @5
    @2
    cB
    cz
    rspcsbela
    expcom
    adantl
    imp
    fsumzcl
    syl5eqel
end
