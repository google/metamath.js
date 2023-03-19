include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "simpll.mm"
include "renegcld.mm"
include "cc.mm"
include "recnd.mm"
include "abscl.mm"
include "syl.mm"
include "simplr.mm"
include "cle.mm"
include "leabs.mm"
include "wceq.mm"
include "absneg.mm"
include "breqtrd.mm"
include "simpr.mm"
include "lelttrd.mm"
include "ad2antrr.mm"
include "jca.mm"
include "ex.mm"
include "wo.mm"
include "wi.mm"
include "absor.mm"
include "adantr.mm"
include "breq1.mm"
include "biimprd.mm"
include "jaoa.mm"
include "ancomsd.mm"
include "impbid.mm"
include "ltnegcon1.mm"
include "anbi1d.mm"
include "bitrd.mm"

theorem abslt
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( abs ` A ) < B <-> ( -u B < A /\ A < B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cabs
    cfv
    #
    cB
    clt
    wbr
    #
    cA
    cneg
    #
    cB
    clt
    wbr
    #
    cA
    cB
    clt
    wbr
    #
    wa
    #
    cB
    cneg
    cA
    clt
    wbr
    #
    @7
    wa
    @2
    @4
    @8
    @2
    @4
    @8
    @2
    @4
    wa
    #
    @6
    @7
    @10
    @5
    @3
    cB
    @10
    cA
    @0
    @1
    @4
    simpll
    #
    renegcld
    #
    @10
    cA
    cc
    wcel
    #
    @3
    cr
    wcel
    @10
    cA
    @11
    recnd
    #
    cA
    abscl
    syl
    #
    @0
    @1
    @4
    simplr
    #
    @10
    @5
    @5
    cabs
    cfv
    #
    @3
    cle
    @10
    @5
    cr
    wcel
    @5
    @17
    cle
    wbr
    @12
    @5
    leabs
    syl
    @10
    @13
    @17
    @3
    wceq
    @14
    cA
    absneg
    syl
    breqtrd
    @2
    @4
    simpr
    #
    lelttrd
    @10
    cA
    @3
    cB
    @11
    @15
    @16
    @0
    cA
    @3
    cle
    wbr
    @1
    @4
    cA
    leabs
    ad2antrr
    @18
    lelttrd
    jca
    ex
    @2
    @3
    cA
    wceq
    #
    @3
    @5
    wceq
    #
    wo
    #
    @8
    @4
    wi
    @0
    @21
    @1
    cA
    absor
    adantr
    @21
    @7
    @6
    @4
    @19
    @7
    @4
    @20
    @6
    @19
    @4
    @7
    @3
    cA
    cB
    clt
    breq1
    biimprd
    @20
    @4
    @6
    @3
    @5
    cB
    clt
    breq1
    biimprd
    jaoa
    ancomsd
    syl
    impbid
    @2
    @6
    @9
    @7
    cA
    cB
    ltnegcon1
    anbi1d
    bitrd
end
