include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "simpl.mm"
include "con3i.mm"
include "ovprc.mm"
include "syl.mm"

theorem ovprc1
  let cA: class A
  let cB: class B
  let cF: class F
  assume ovprc1.1: |- Rel dom F


  assert |- ( -. A e. _V -> ( A F B ) = (/) )

  proof
    cA
    cvv
    wcel
    #
    wn
    @0
    cB
    cvv
    wcel
    #
    wa
    #
    wn
    cA
    cB
    cF
    co
    c0
    wceq
    @2
    @0
    @0
    @1
    simpl
    con3i
    cA
    cB
    cF
    ovprc1.1
    ovprc
    syl
end
