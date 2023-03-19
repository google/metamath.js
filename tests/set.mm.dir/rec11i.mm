include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "rec11.mm"
include "an4s.mm"
include "mpanl12.mm"

theorem rec11i
  let cA: class A
  let cB: class B
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC


  assert |- ( ( A =/= 0 /\ B =/= 0 ) -> ( ( 1 / A ) = ( 1 / B ) <-> A = B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cB
    cc0
    wne
    #
    wa
    c1
    cA
    cdiv
    co
    c1
    cB
    cdiv
    co
    wceq
    cA
    cB
    wceq
    wb
    #
    divclz.1
    divclz.2
    @0
    @2
    @1
    @3
    @4
    cA
    cB
    rec11
    an4s
    mpanl12
end
