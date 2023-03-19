include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "chlejb1.mm"
include "chjcom.mm"
include "eqeq1d.mm"
include "bitrd.mm"

theorem chlejb2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A C_ B <-> ( B vH A ) = B ) )

  proof
    cA
    cch
    wcel
    cB
    cch
    wcel
    wa
    #
    cA
    cB
    wss
    cA
    cB
    chj
    co
    #
    cB
    wceq
    cB
    cA
    chj
    co
    #
    cB
    wceq
    cA
    cB
    chlejb1
    @0
    @1
    @2
    cB
    cA
    cB
    chjcom
    eqeq1d
    bitrd
end
