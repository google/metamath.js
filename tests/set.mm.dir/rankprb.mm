include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cun.mm"
include "crnk.mm"
include "cfv.mm"
include "csuc.mm"
include "cpr.mm"
include "wceq.mm"
include "snwf.mm"
include "rankunb.mm"
include "syl2an.mm"
include "ranksnb.mm"
include "uneq12.mm"
include "eqtrd.mm"
include "df-pr.mm"
include "fveq2i.mm"
include "word.mm"
include "rankon.mm"
include "onordi.mm"
include "ordsucun.mm"
include "mp2an.mm"
include "3eqtr4g.mm"

theorem rankprb
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. U. ( R1 " On ) /\ B e. U. ( R1 " On ) ) -> ( rank ` { A , B } ) = suc ( ( rank ` A ) u. ( rank ` B ) ) )

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
    csn
    #
    cB
    csn
    #
    cun
    #
    crnk
    cfv
    #
    cA
    crnk
    cfv
    #
    csuc
    #
    cB
    crnk
    cfv
    #
    csuc
    #
    cun
    #
    cA
    cB
    cpr
    #
    crnk
    cfv
    @8
    @10
    cun
    csuc
    #
    @3
    @7
    @4
    crnk
    cfv
    #
    @5
    crnk
    cfv
    #
    cun
    #
    @12
    @1
    @4
    @0
    wcel
    @5
    @0
    wcel
    @7
    @17
    wceq
    @2
    cA
    snwf
    cB
    snwf
    @4
    @5
    rankunb
    syl2an
    @1
    @15
    @9
    wceq
    @16
    @11
    wceq
    @17
    @12
    wceq
    @2
    cA
    ranksnb
    cB
    ranksnb
    @15
    @9
    @16
    @11
    uneq12
    syl2an
    eqtrd
    @13
    @6
    crnk
    cA
    cB
    df-pr
    fveq2i
    @8
    word
    @10
    word
    @14
    @12
    wceq
    @8
    cA
    rankon
    onordi
    @10
    cB
    rankon
    onordi
    @8
    @10
    ordsucun
    mp2an
    3eqtr4g
end
