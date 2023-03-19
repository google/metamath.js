include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "crnk.mm"
include "cfv.mm"
include "csn.mm"
include "cpr.mm"
include "cun.mm"
include "csuc.mm"
include "dfopg.mm"
include "fveq2d.mm"
include "wceq.mm"
include "snwf.mm"
include "adantr.mm"
include "prwf.mm"
include "rankprb.mm"
include "syl2anc.mm"
include "wss.mm"
include "snsspr1.mm"
include "ssequn1.mm"
include "mpbi.mm"
include "fveq2i.mm"
include "rankunb.mm"
include "3eqtr3a.mm"
include "suceq.mm"
include "syl.mm"
include "3eqtrd.mm"

theorem rankopb
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. U. ( R1 " On ) /\ B e. U. ( R1 " On ) ) -> ( rank ` <. A , B >. ) = suc suc ( ( rank ` A ) u. ( rank ` B ) ) )

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
    #
    cA
    cB
    cop
    #
    crnk
    cfv
    cA
    csn
    #
    cA
    cB
    cpr
    #
    cpr
    #
    crnk
    cfv
    #
    @5
    crnk
    cfv
    @6
    crnk
    cfv
    #
    cun
    #
    csuc
    #
    cA
    crnk
    cfv
    cB
    crnk
    cfv
    cun
    csuc
    #
    csuc
    #
    @3
    @4
    @7
    crnk
    cA
    cB
    @0
    @0
    dfopg
    fveq2d
    @3
    @5
    @0
    wcel
    #
    @6
    @0
    wcel
    #
    @8
    @11
    wceq
    @1
    @14
    @2
    cA
    snwf
    adantr
    #
    cA
    cB
    prwf
    #
    @5
    @6
    rankprb
    syl2anc
    @3
    @10
    @12
    wceq
    @11
    @13
    wceq
    @3
    @5
    @6
    cun
    #
    crnk
    cfv
    #
    @9
    @10
    @12
    @18
    @6
    crnk
    @5
    @6
    wss
    @18
    @6
    wceq
    cA
    cB
    snsspr1
    @5
    @6
    ssequn1
    mpbi
    fveq2i
    @3
    @14
    @15
    @19
    @10
    wceq
    @16
    @17
    @5
    @6
    rankunb
    syl2anc
    cA
    cB
    rankprb
    3eqtr3a
    @10
    @12
    suceq
    syl
    3eqtrd
end
