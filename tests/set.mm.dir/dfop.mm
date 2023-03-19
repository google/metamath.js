include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "cpr.mm"
include "wceq.mm"
include "dfopg.mm"
include "mp2an.mm"

theorem dfop
  let cA: class A
  let cB: class B
  assume dfop.1: |- A e. _V
  assume dfop.2: |- B e. _V


  assert |- <. A , B >. = { { A } , { A , B } }

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cop
    cA
    csn
    cA
    cB
    cpr
    cpr
    wceq
    dfop.1
    dfop.2
    cA
    cB
    cvv
    cvv
    dfopg
    mp2an
end
