include "wss.mm"
include "cin.mm"
include "inass.mm"
include "wceq.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "ineq2d.mm"
include "syl5eq.mm"

theorem inabs3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( C C_ B -> ( ( A i^i B ) i^i C ) = ( A i^i C ) )

  proof
    cC
    cB
    wss
    #
    cA
    cB
    cin
    cC
    cin
    cA
    cB
    cC
    cin
    #
    cin
    cA
    cC
    cin
    cA
    cB
    cC
    inass
    @0
    @1
    cC
    cA
    @0
    @1
    cC
    wceq
    cC
    cB
    sseqin2
    biimpi
    ineq2d
    syl5eq
end
