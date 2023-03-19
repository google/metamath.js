include "cz.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wrex.mm"
include "cc0.mm"
include "cico.mm"
include "cr.mm"
include "zre.mm"
include "modelico.mm"
include "sylan.mm"
include "adantr.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbid.mm"
include "simpll.mm"
include "simpr.mm"
include "modmuladd.mm"
include "syl3anc.mm"
include "biimpd.mm"
include "impancom.mm"
include "mpd.mm"
include "ex.mm"

theorem modmuladdim
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M

  disjoint A k
  disjoint B k
  disjoint M k
  assert |- ( ( A e. ZZ /\ M e. RR+ ) -> ( ( A mod M ) = B -> E. k e. ZZ A = ( ( k x. M ) + B ) ) )

  proof
    cA
    cz
    wcel
    #
    cM
    crp
    wcel
    #
    wa
    #
    cA
    cM
    cmo
    co
    #
    cB
    wceq
    #
    cA
    vk
    cv
    cM
    cmul
    co
    cB
    caddc
    co
    wceq
    vk
    cz
    wrex
    #
    @2
    @4
    wa
    #
    cB
    cc0
    cM
    cico
    co
    #
    wcel
    #
    @5
    @6
    @3
    @7
    wcel
    #
    @8
    @2
    @9
    @4
    @0
    cA
    cr
    wcel
    @1
    @9
    cA
    zre
    cA
    cM
    modelico
    sylan
    adantr
    @4
    @9
    @8
    wb
    @2
    @3
    cB
    @7
    eleq1
    adantl
    mpbid
    @2
    @8
    @4
    @5
    @2
    @8
    wa
    #
    @4
    @5
    @10
    @0
    @8
    @1
    @4
    @5
    wb
    @0
    @1
    @8
    simpll
    @2
    @8
    simpr
    @2
    @1
    @8
    @0
    @1
    simpr
    adantr
    cA
    cB
    vk
    cM
    modmuladd
    syl3anc
    biimpd
    impancom
    mpd
    ex
end
