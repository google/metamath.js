include "cotp.mm"
include "wceq.mm"
include "cop.mm"
include "w3a.mm"
include "df-ot.mm"
include "eqeq12i.mm"
include "otth2.mm"
include "bitri.mm"

theorem otth
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  assume otth.1: |- A e. _V
  assume otth.2: |- B e. _V
  assume otth.3: |- R e. _V


  assert |- ( <. A , B , R >. = <. C , D , S >. <-> ( A = C /\ B = D /\ R = S ) )

  proof
    cA
    cB
    cR
    cotp
    #
    cC
    cD
    cS
    cotp
    #
    wceq
    cA
    cB
    cop
    cR
    cop
    #
    cC
    cD
    cop
    cS
    cop
    #
    wceq
    cA
    cC
    wceq
    cB
    cD
    wceq
    cR
    cS
    wceq
    w3a
    @0
    @2
    @1
    @3
    cA
    cB
    cR
    df-ot
    cC
    cD
    cS
    df-ot
    eqeq12i
    cA
    cB
    cC
    cD
    cR
    cS
    otth.1
    otth.2
    otth.3
    otth2
    bitri
end
