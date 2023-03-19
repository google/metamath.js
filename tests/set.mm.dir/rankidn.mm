include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "wn.mm"
include "csuc.mm"
include "wceq.mm"
include "wa.mm"
include "eqid.mm"
include "rankr1c.mm"
include "mpbii.mm"
include "simpld.mm"

theorem rankidn
  let cA: class A


  assert |- ( A e. U. ( R1 " On ) -> -. A e. ( R1 ` ( rank ` A ) ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    wcel
    #
    cA
    cA
    crnk
    cfv
    #
    cr1
    cfv
    wcel
    wn
    #
    cA
    @1
    csuc
    cr1
    cfv
    wcel
    #
    @0
    @1
    @1
    wceq
    @2
    @3
    wa
    @1
    eqid
    cA
    @1
    rankr1c
    mpbii
    simpld
end
