include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wn.mm"
include "c0.mm"
include "ndmov.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "con4i.mm"

theorem ndmovrcl
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  assume ndmov.1: |- dom F = ( S X. S )
  assume ndmovrcl.3: |- -. (/) e. S


  assert |- ( ( A F B ) e. S -> ( A e. S /\ B e. S ) )

  proof
    cA
    cS
    wcel
    cB
    cS
    wcel
    wa
    #
    cA
    cB
    cF
    co
    #
    cS
    wcel
    #
    @0
    wn
    #
    @2
    c0
    cS
    wcel
    ndmovrcl.3
    @3
    @1
    c0
    cS
    cA
    cB
    cS
    cF
    ndmov.1
    ndmov
    eleq1d
    mtbiri
    con4i
end
