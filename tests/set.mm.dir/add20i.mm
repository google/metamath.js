include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "add20.mm"
include "an4s.mm"
include "mpanl12.mm"

theorem add20i
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR


  assert |- ( ( 0 <_ A /\ 0 <_ B ) -> ( ( A + B ) = 0 <-> ( A = 0 /\ B = 0 ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
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
    wa
    cA
    cB
    caddc
    co
    cc0
    wceq
    cA
    cc0
    wceq
    cB
    cc0
    wceq
    wa
    wb
    #
    lt2.1
    lt2.2
    @0
    @2
    @1
    @3
    @4
    cA
    cB
    add20
    an4s
    mpanl12
end
