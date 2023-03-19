include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "elrp.mm"
include "mpbir2an.mm"

theorem elrpii
  let cA: class A
  assume elrpi.1: |- A e. RR
  assume elrpi.2: |- 0 < A


  assert |- A e. RR+

  proof
    cA
    crp
    wcel
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    elrpi.1
    elrpi.2
    cA
    elrp
    mpbir2an
end
