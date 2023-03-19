include "cfn.mm"
include "wcel.mm"
include "cz.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "wral.mm"
include "wa.mm"
include "csu.mm"
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

theorem fsummsnunzOLD
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
  assert |- ( ( A e. Fin /\ A. k e. ( A u. { z } ) B e. ZZ ) -> sum_ k e. ( A u. { z } ) B e. ZZ )

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
    vz
    cv
    #
    csn
    #
    cun
    #
    wral
    #
    wa
    #
    @3
    cB
    vk
    csu
    @3
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
    @3
    cB
    @7
    vk
    vx
    vx
    cB
    nfcv
    vk
    @6
    cB
    nfcsb1v
    vk
    @6
    cB
    csbeq1a
    cbvsumi
    @5
    @3
    @7
    vx
    @0
    @4
    @2
    cfn
    wcel
    #
    @3
    cfn
    wcel
    @8
    @5
    @1
    snfi
    a1i
    cA
    @2
    unfi
    syldan
    @5
    @6
    @3
    wcel
    #
    @7
    cz
    wcel
    #
    @4
    @9
    @10
    wi
    @0
    @9
    @4
    @10
    vk
    @6
    @3
    cB
    cz
    rspcsbela
    expcom
    adantl
    imp
    fsumzcl
    syl5eqel
end
