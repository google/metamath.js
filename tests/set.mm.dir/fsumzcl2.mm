include "cfn.mm"
include "wcel.mm"
include "cz.mm"
include "wral.mm"
include "wa.mm"
include "csu.mm"
include "cv.mm"
include "csb.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
include "simpl.mm"
include "wi.mm"
include "rspcsbela.mm"
include "expcom.mm"
include "adantl.mm"
include "imp.mm"
include "fsumzcl.mm"
include "syl5eqel.mm"

theorem fsumzcl2
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint B x
  assert |- ( ( A e. Fin /\ A. k e. A B e. ZZ ) -> sum_ k e. A B e. ZZ )

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
    wral
    #
    wa
    #
    cA
    cB
    vk
    csu
    cA
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
    cA
    cB
    @4
    vk
    vx
    vx
    cB
    nfcv
    vk
    @3
    cB
    nfcsb1v
    vk
    @3
    cB
    csbeq1a
    cbvsumi
    @2
    cA
    @4
    vx
    @0
    @1
    simpl
    @2
    @3
    cA
    wcel
    #
    @4
    cz
    wcel
    #
    @1
    @5
    @6
    wi
    @0
    @5
    @1
    @6
    vk
    @3
    cA
    cB
    cz
    rspcsbela
    expcom
    adantl
    imp
    fsumzcl
    syl5eqel
end
