include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "csqrt.mm"
include "cfv.mm"
include "resqrtcl.mm"
include "mpan.mm"

theorem sqrtcli
  let cA: class A
  assume sqrth.1: |- A e. RR


  assert |- ( 0 <_ A -> ( sqrt ` A ) e. RR )

  proof
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cA
    csqrt
    cfv
    cr
    wcel
    sqrth.1
    cA
    resqrtcl
    mpan
end
