include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "caltop.mm"
include "crnk.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "csuc.mm"
include "wceq.mm"
include "snwf.mm"
include "cpr.mm"
include "df-altop.mm"
include "fveq2i.mm"
include "adantr.mm"
include "prwf.mm"
include "rankprb.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "wss.mm"
include "snsspr1.mm"
include "ssequn1.mm"
include "mpbi.mm"
include "rankunb.mm"
include "3eqtr3a.mm"
include "suceq.mm"
include "syl.mm"
include "eqtrd.mm"
include "sylan2.mm"
include "ranksnb.mm"
include "uneq2d.mm"
include "3syl.mm"
include "adantl.mm"

theorem rankaltopb
  let cA: class A
  let cB: class B


  assert |- ( ( A e. U. ( R1 " On ) /\ B e. U. ( R1 " On ) ) -> ( rank ` << A , B >> ) = suc suc ( ( rank ` A ) u. suc ( rank ` B ) ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    cA
    cB
    caltop
    #
    crnk
    cfv
    #
    cA
    crnk
    cfv
    #
    cB
    csn
    #
    crnk
    cfv
    #
    cun
    #
    csuc
    #
    csuc
    #
    @5
    cB
    crnk
    cfv
    csuc
    #
    cun
    #
    csuc
    #
    csuc
    #
    @2
    @1
    @6
    @0
    wcel
    #
    @4
    @10
    wceq
    cB
    snwf
    @1
    @15
    wa
    #
    @4
    cA
    csn
    #
    crnk
    cfv
    cA
    @6
    cpr
    #
    crnk
    cfv
    #
    cun
    #
    csuc
    #
    @10
    @16
    @4
    @17
    @18
    cpr
    #
    crnk
    cfv
    #
    @21
    @3
    @22
    crnk
    cA
    cB
    df-altop
    fveq2i
    @16
    @17
    @0
    wcel
    #
    @18
    @0
    wcel
    #
    @23
    @21
    wceq
    @1
    @24
    @15
    cA
    snwf
    adantr
    #
    cA
    @6
    prwf
    #
    @17
    @18
    rankprb
    syl2anc
    syl5eq
    @16
    @20
    @9
    wceq
    @21
    @10
    wceq
    @16
    @17
    @18
    cun
    #
    crnk
    cfv
    #
    @19
    @20
    @9
    @28
    @18
    crnk
    @17
    @18
    wss
    @28
    @18
    wceq
    cA
    @6
    snsspr1
    @17
    @18
    ssequn1
    mpbi
    fveq2i
    @16
    @24
    @25
    @29
    @20
    wceq
    @26
    @27
    @17
    @18
    rankunb
    syl2anc
    cA
    @6
    rankprb
    3eqtr3a
    @20
    @9
    suceq
    syl
    eqtrd
    sylan2
    @2
    @10
    @14
    wceq
    #
    @1
    @2
    @8
    @12
    wceq
    @9
    @13
    wceq
    @30
    @2
    @7
    @11
    @5
    cB
    ranksnb
    uneq2d
    @8
    @12
    suceq
    @9
    @13
    suceq
    3syl
    adantl
    eqtrd
end
