include "cfn.mm"
include "wcel.mm"
include "cz.mm"
include "wral.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "csu.mm"
include "cv.mm"
include "csb.mm"
include "cr.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
include "diffi.mm"
include "adantr.mm"
include "wi.mm"
include "eldifi.mm"
include "rspcsbela.mm"
include "sylan.mm"
include "zred.mm"
include "expcom.mm"
include "adantl.mm"
include "imp.mm"
include "fsumrecl.mm"
include "syl5eqel.mm"

theorem fsummsndifre
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cX: class X
  let vx: setvar x

  disjoint A k
  disjoint X k
  disjoint A x
  disjoint k x
  disjoint B x
  disjoint X x
  disjoint k x
  assert |- ( ( A e. Fin /\ A. k e. A B e. ZZ ) -> sum_ k e. ( A \ { X } ) B e. RR )

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
    cX
    csn
    #
    cdif
    #
    cB
    vk
    csu
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
    cr
    @4
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
    @2
    @4
    @6
    vx
    @0
    @4
    cfn
    wcel
    @1
    cA
    @3
    diffi
    adantr
    @2
    @5
    @4
    wcel
    #
    @6
    cr
    wcel
    #
    @1
    @7
    @8
    wi
    @0
    @7
    @1
    @8
    @7
    @1
    wa
    @6
    @7
    @5
    cA
    wcel
    @1
    @6
    cz
    wcel
    @5
    cA
    @3
    eldifi
    vk
    @5
    cA
    cB
    cz
    rspcsbela
    sylan
    zred
    expcom
    adantl
    imp
    fsumrecl
    syl5eqel
end
