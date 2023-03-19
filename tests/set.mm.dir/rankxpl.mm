include "cxp.mm"
include "c0.mm"
include "wne.mm"
include "cun.mm"
include "crnk.mm"
include "cfv.mm"
include "cuni.mm"
include "unixp.mm"
include "fveq2d.mm"
include "xpex.mm"
include "uniex.mm"
include "rankuniss.mm"
include "sstri.mm"
include "syl6eqssr.mm"

theorem rankxpl
  let cA: class A
  let cB: class B
  assume rankxpl.1: |- A e. _V
  assume rankxpl.2: |- B e. _V


  assert |- ( ( A X. B ) =/= (/) -> ( rank ` ( A u. B ) ) C_ ( rank ` ( A X. B ) ) )

  proof
    cA
    cB
    cxp
    #
    c0
    wne
    #
    cA
    cB
    cun
    #
    crnk
    cfv
    @0
    cuni
    #
    cuni
    #
    crnk
    cfv
    #
    @0
    crnk
    cfv
    #
    @1
    @4
    @2
    crnk
    cA
    cB
    unixp
    fveq2d
    @5
    @3
    crnk
    cfv
    @6
    @3
    @0
    cA
    cB
    rankxpl.1
    rankxpl.2
    xpex
    #
    uniex
    rankuniss
    @0
    @7
    rankuniss
    sstri
    syl6eqssr
end
