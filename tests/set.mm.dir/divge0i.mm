include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cdiv.mm"
include "co.mm"
include "wa.mm"
include "divge0.mm"
include "mpanr1.mm"
include "mpanl1.mm"

theorem divge0i
  let cA: class A
  let cB: class B
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR


  assert |- ( ( 0 <_ A /\ 0 < B ) -> 0 <_ ( A / B ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
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
    cle
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
    divge0
    mpanr1
    mpanl1
end
