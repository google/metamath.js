include "cvv.mm"
include "wcel.mm"
include "cec.mm"
include "wbr.mm"
include "wb.mm"
include "elecg.mm"
include "mp2an.mm"

theorem elec
  let cA: class A
  let cB: class B
  let cR: class R
  assume elec.1: |- A e. _V
  assume elec.2: |- B e. _V


  assert |- ( A e. [ B ] R <-> B R A )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cR
    cec
    wcel
    cB
    cA
    cR
    wbr
    wb
    elec.1
    elec.2
    cA
    cB
    cR
    cvv
    cvv
    elecg
    mp2an
end
