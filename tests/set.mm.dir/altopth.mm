include "cvv.mm"
include "wcel.mm"
include "caltop.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "altopthg.mm"
include "mp2an.mm"

theorem altopth
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume altopth.1: |- A e. _V
  assume altopth.2: |- B e. _V


  assert |- ( << A , B >> = << C , D >> <-> ( A = C /\ B = D ) )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    caltop
    cC
    cD
    caltop
    wceq
    cA
    cC
    wceq
    cB
    cD
    wceq
    wa
    wb
    altopth.1
    altopth.2
    cA
    cB
    cC
    cD
    cvv
    cvv
    altopthg
    mp2an
end
