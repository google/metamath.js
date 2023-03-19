include "cvv.mm"
include "wcel.mm"
include "caltop.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "altopthbg.mm"
include "mp2an.mm"

theorem altopthb
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume altopthb.1: |- A e. _V
  assume altopthb.2: |- D e. _V


  assert |- ( << A , B >> = << C , D >> <-> ( A = C /\ B = D ) )

  proof
    cA
    cvv
    wcel
    cD
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
    altopthb.1
    altopthb.2
    cA
    cB
    cC
    cD
    cvv
    cvv
    altopthbg
    mp2an
end
