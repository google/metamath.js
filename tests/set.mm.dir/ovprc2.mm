include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "simpr.mm"
include "con3i.mm"
include "ovprc.mm"
include "syl.mm"

theorem ovprc2
  let cA: class A
  let cB: class B
  let cF: class F
  assume ovprc1.1: |- Rel dom F


  assert |- ( -. B e. _V -> ( A F B ) = (/) )

  proof
    cB
    cvv
    wcel
    #
    wn
    cA
    cvv
    wcel
    #
    @0
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
    @1
    @0
    simpr
    con3i
    cA
    cB
    cF
    ovprc1.1
    ovprc
    syl
end
