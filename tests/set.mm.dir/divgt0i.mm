include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "wa.mm"
include "divgt0.mm"
include "mpanr1.mm"
include "mpanl1.mm"

theorem divgt0i
  let cA: class A
  let cB: class B
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR


  assert |- ( ( 0 < A /\ 0 < B ) -> 0 < ( A / B ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    cc0
    cB
    clt
    wbr
    #
    cc0
    cA
    cB
    cdiv
    co
    clt
    wbr
    #
    ltplus1.1
    @0
    @1
    wa
    cB
    cr
    wcel
    @2
    @3
    prodgt0.2
    cA
    cB
    divgt0
    mpanr1
    mpanl1
end
