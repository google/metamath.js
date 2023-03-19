include "wcel.mm"
include "csn.mm"
include "cin.mm"
include "wceq.mm"
include "wa.mm"
include "snidg.mm"
include "eleq2.mm"
include "elin.mm"
include "biimpi.mm"
include "syl6bir.mm"
include "mpan9.mm"

theorem elinsn
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( ( A e. V /\ ( B i^i C ) = { A } ) -> ( A e. B /\ A e. C ) )

  proof
    cA
    cV
    wcel
    cA
    cA
    csn
    #
    wcel
    #
    cB
    cC
    cin
    #
    @0
    wceq
    #
    cA
    cB
    wcel
    cA
    cC
    wcel
    wa
    #
    cA
    cV
    snidg
    @3
    @1
    cA
    @2
    wcel
    #
    @4
    @2
    @0
    cA
    eleq2
    @5
    @4
    cA
    cB
    cC
    elin
    biimpi
    syl6bir
    mpan9
end
