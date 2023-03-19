include "word.mm"
include "wa.mm"
include "wcel.mm"
include "wo.mm"
include "wn.mm"
include "wss.mm"
include "nelss.mm"
include "adantl.mm"
include "wb.mm"
include "ordtri1.mm"
include "con2bid.mm"
include "adantr.mm"
include "mpbird.mm"
include "expr.mm"
include "orrd.mm"
include "ex.mm"

theorem ordtr3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( Ord B /\ Ord C ) -> ( A e. B -> ( A e. C \/ C e. B ) ) )

  proof
    cB
    word
    cC
    word
    wa
    #
    cA
    cB
    wcel
    #
    cA
    cC
    wcel
    #
    cC
    cB
    wcel
    #
    wo
    @0
    @1
    wa
    @2
    @3
    @0
    @1
    @2
    wn
    #
    @3
    @0
    @1
    @4
    wa
    #
    wa
    @3
    cB
    cC
    wss
    #
    wn
    #
    @5
    @7
    @0
    cA
    cB
    cC
    nelss
    adantl
    @0
    @3
    @7
    wb
    @5
    @0
    @6
    @3
    cB
    cC
    ordtri1
    con2bid
    adantr
    mpbird
    expr
    orrd
    ex
end
