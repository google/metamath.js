include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "wa.mm"
include "lerec.mm"
include "mpanr1.mm"
include "mpanl1.mm"

theorem lereci
  let cA: class A
  let cB: class B
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR


  assert |- ( ( 0 < A /\ 0 < B ) -> ( A <_ B <-> ( 1 / B ) <_ ( 1 / A ) ) )

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
    cA
    cB
    cle
    wbr
    c1
    cB
    cdiv
    co
    c1
    cA
    cdiv
    co
    cle
    wbr
    wb
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
    lerec
    mpanr1
    mpanl1
end
