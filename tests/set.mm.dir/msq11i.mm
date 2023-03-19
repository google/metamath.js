include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "msq11.mm"
include "mpanr1.mm"
include "mpanl1.mm"

theorem msq11i
  let cA: class A
  let cB: class B
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR


  assert |- ( ( 0 <_ A /\ 0 <_ B ) -> ( ( A x. A ) = ( B x. B ) <-> A = B ) )

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
    cle
    wbr
    #
    cA
    cA
    cmul
    co
    cB
    cB
    cmul
    co
    wceq
    cA
    cB
    wceq
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
    msq11
    mpanr1
    mpanl1
end
