include "caltop.mm"
include "wceq.mm"
include "wa.mm"
include "eqcom.mm"
include "altopthb.mm"
include "anbi12i.mm"
include "3bitri.mm"

theorem altopthc
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume altopthc.1: |- B e. _V
  assume altopthc.2: |- C e. _V


  assert |- ( << A , B >> = << C , D >> <-> ( A = C /\ B = D ) )

  proof
    cA
    cB
    caltop
    #
    cC
    cD
    caltop
    #
    wceq
    @1
    @0
    wceq
    cC
    cA
    wceq
    #
    cD
    cB
    wceq
    #
    wa
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    @0
    @1
    eqcom
    cC
    cD
    cA
    cB
    altopthc.2
    altopthc.1
    altopthb
    @2
    @4
    @3
    @5
    cC
    cA
    eqcom
    cD
    cB
    eqcom
    anbi12i
    3bitri
end
