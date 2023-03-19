include "c0.mm"
include "cec.mm"
include "csn.mm"
include "cima.mm"
include "df-ec.mm"
include "0ima.mm"
include "eqtri.mm"

theorem ec0
  let cA: class A


  assert |- [ A ] (/) = (/)

  proof
    cA
    c0
    cec
    c0
    cA
    csn
    #
    cima
    c0
    cA
    c0
    df-ec
    @0
    0ima
    eqtri
end
