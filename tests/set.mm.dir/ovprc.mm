include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "co.mm"
include "cop.mm"
include "cfv.mm"
include "c0.mm"
include "df-ov.mm"
include "cdm.mm"
include "wceq.mm"
include "wbr.mm"
include "df-br.mm"
include "wrel.mm"
include "brrelex12.mm"
include "mpan.mm"
include "sylbir.mm"
include "con3i.mm"
include "ndmfv.mm"
include "syl.mm"
include "syl5eq.mm"

theorem ovprc
  let cA: class A
  let cB: class B
  let cF: class F
  assume ovprc1.1: |- Rel dom F


  assert |- ( -. ( A e. _V /\ B e. _V ) -> ( A F B ) = (/) )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    #
    wn
    #
    cA
    cB
    cF
    co
    cA
    cB
    cop
    #
    cF
    cfv
    #
    c0
    cA
    cB
    cF
    df-ov
    @1
    @2
    cF
    cdm
    #
    wcel
    #
    wn
    @3
    c0
    wceq
    @5
    @0
    @5
    cA
    cB
    @4
    wbr
    #
    @0
    cA
    cB
    @4
    df-br
    @4
    wrel
    @6
    @0
    ovprc1.1
    cA
    cB
    @4
    brrelex12
    mpan
    sylbir
    con3i
    @2
    cF
    ndmfv
    syl
    syl5eq
end
