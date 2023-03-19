include "wcel.mm"
include "cep.mm"
include "ccnv.mm"
include "cec.mm"
include "cv.mm"
include "eleccnvep.mm"
include "eqrdv.mm"

theorem eccnvep
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> [ A ] `' _E = A )

  proof
    cA
    cV
    wcel
    vx
    cA
    cep
    ccnv
    cec
    cA
    cA
    vx
    cv
    cV
    eleccnvep
    eqrdv
end
