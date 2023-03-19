include "caltop.mm"
include "wceq.mm"
include "wa.mm"
include "eqcom.mm"
include "altopth.mm"
include "anbi12i.mm"
include "3bitri.mm"

theorem altopthd
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume altopthd.1: |- C e. _V
  assume altopthd.2: |- D e. _V


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
    altopthd.1
    altopthd.2
    altopth
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
