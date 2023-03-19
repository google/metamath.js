include "cop.mm"
include "ctp.mm"
include "wbr.mm"
include "wcel.mm"
include "wceq.mm"
include "w3o.mm"
include "wa.mm"
include "df-br.mm"
include "opex.mm"
include "eltp.mm"
include "opth.mm"
include "3orbi123i.mm"
include "3bitri.mm"

theorem brtp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cX: class X
  let cY: class Y
  assume brtp.1: |- X e. _V
  assume brtp.2: |- Y e. _V


  assert |- ( X { <. A , B >. , <. C , D >. , <. E , F >. } Y <-> ( ( X = A /\ Y = B ) \/ ( X = C /\ Y = D ) \/ ( X = E /\ Y = F ) ) )

  proof
    cX
    cY
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cE
    cF
    cop
    #
    ctp
    #
    wbr
    cX
    cY
    cop
    #
    @3
    wcel
    @4
    @0
    wceq
    #
    @4
    @1
    wceq
    #
    @4
    @2
    wceq
    #
    w3o
    cX
    cA
    wceq
    cY
    cB
    wceq
    wa
    #
    cX
    cC
    wceq
    cY
    cD
    wceq
    wa
    #
    cX
    cE
    wceq
    cY
    cF
    wceq
    wa
    #
    w3o
    cX
    cY
    @3
    df-br
    @4
    @0
    @1
    @2
    cX
    cY
    opex
    eltp
    @5
    @8
    @6
    @9
    @7
    @10
    cX
    cY
    cA
    cB
    brtp.1
    brtp.2
    opth
    cX
    cY
    cC
    cD
    brtp.1
    brtp.2
    opth
    cX
    cY
    cE
    cF
    brtp.1
    brtp.2
    opth
    3orbi123i
    3bitri
end
