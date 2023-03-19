include "csuc.mm"
include "crnk.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "df-suc.mm"
include "fveq2i.mm"
include "snex.mm"
include "rankun.mm"
include "ranksn.mm"
include "uneq2i.mm"
include "wss.mm"
include "wceq.mm"
include "sssucid.mm"
include "ssequn1.mm"
include "mpbi.mm"
include "eqtri.mm"

theorem ranksuc
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  assume rankr1b.1: |- A e. _V


  assert |- ( rank ` suc A ) = suc ( rank ` A )

  proof
    cA
    csuc
    #
    crnk
    cfv
    cA
    cA
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
    @0
    @2
    crnk
    cA
    df-suc
    fveq2i
    @3
    @4
    @1
    crnk
    cfv
    #
    cun
    #
    @5
    cA
    @1
    rankr1b.1
    cA
    snex
    rankun
    @7
    @4
    @5
    cun
    #
    @5
    @6
    @5
    @4
    cA
    rankr1b.1
    ranksn
    uneq2i
    @4
    @5
    wss
    @8
    @5
    wceq
    @4
    sssucid
    @4
    @5
    ssequn1
    mpbi
    eqtri
    eqtri
    eqtri
end
