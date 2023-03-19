include "wne.mm"
include "w3a.mm"
include "wn.mm"
include "w3o.mm"
include "wceq.mm"
include "3anor.mm"
include "nne.mm"
include "3orbi123i.mm"
include "xchbinx.mm"

theorem ne3anior
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F


  assert |- ( ( A =/= B /\ C =/= D /\ E =/= F ) <-> -. ( A = B \/ C = D \/ E = F ) )

  proof
    cA
    cB
    wne
    #
    cC
    cD
    wne
    #
    cE
    cF
    wne
    #
    w3a
    @0
    wn
    #
    @1
    wn
    #
    @2
    wn
    #
    w3o
    cA
    cB
    wceq
    #
    cC
    cD
    wceq
    #
    cE
    cF
    wceq
    #
    w3o
    @0
    @1
    @2
    3anor
    @3
    @6
    @4
    @7
    @5
    @8
    cA
    cB
    nne
    cC
    cD
    nne
    cE
    cF
    nne
    3orbi123i
    xchbinx
end
