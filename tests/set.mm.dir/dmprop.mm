include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "cpr.mm"
include "cdm.mm"
include "wceq.mm"
include "dmpropg.mm"
include "mp2an.mm"

theorem dmprop
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume dmsnop.1: |- B e. _V
  assume dmprop.1: |- D e. _V


  assert |- dom { <. A , B >. , <. C , D >. } = { A , C }

  proof
    cB
    cvv
    wcel
    cD
    cvv
    wcel
    cA
    cB
    cop
    cC
    cD
    cop
    cpr
    cdm
    cA
    cC
    cpr
    wceq
    dmsnop.1
    dmprop.1
    cA
    cB
    cC
    cD
    cvv
    cvv
    dmpropg
    mp2an
end
