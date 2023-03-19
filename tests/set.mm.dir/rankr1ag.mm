include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "crnk.mm"
include "rankr1ai.mm"
include "csuc.mm"
include "wss.mm"
include "word.mm"
include "wi.mm"
include "wlim.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limord.mm"
include "ax-mp.mm"
include "ordelord.mm"
include "mpan.mm"
include "adantl.mm"
include "ordsucss.mm"
include "syl.mm"
include "rankidb.mm"
include "elfvdm.mm"
include "r1ord3g.mm"
include "sylan.mm"
include "adantr.mm"
include "ssel.mm"
include "syl5com.mm"
include "3syld.mm"
include "impbid2.mm"

theorem rankr1ag
  let cA: class A
  let cB: class B


  assert |- ( ( A e. U. ( R1 " On ) /\ B e. dom R1 ) -> ( A e. ( R1 ` B ) <-> ( rank ` A ) e. B ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    wcel
    #
    cB
    cr1
    cdm
    #
    wcel
    #
    wa
    #
    cA
    cB
    cr1
    cfv
    #
    wcel
    #
    cA
    crnk
    cfv
    #
    cB
    wcel
    #
    cA
    cB
    rankr1ai
    @3
    @7
    @6
    csuc
    #
    cB
    wss
    #
    @8
    cr1
    cfv
    #
    @4
    wss
    #
    @5
    @3
    cB
    word
    #
    @7
    @9
    wi
    @2
    @12
    @0
    @1
    word
    #
    @2
    @12
    @1
    wlim
    #
    @13
    cr1
    wfun
    @14
    r1funlim
    simpri
    @1
    limord
    ax-mp
    @1
    cB
    ordelord
    mpan
    adantl
    @6
    cB
    ordsucss
    syl
    @0
    @8
    @1
    wcel
    #
    @2
    @9
    @11
    wi
    @0
    cA
    @10
    wcel
    #
    @15
    cA
    rankidb
    #
    cA
    @8
    cr1
    elfvdm
    syl
    @8
    cB
    r1ord3g
    sylan
    @3
    @16
    @11
    @5
    @0
    @16
    @2
    @17
    adantr
    @10
    @4
    cA
    ssel
    syl5com
    3syld
    impbid2
end
