include "cr.mm"
include "wcel.mm"
include "cxne.mm"
include "cneg.mm"
include "rexneg.mm"
include "renegcl.mm"
include "eqeltrd.mm"

theorem xnegrecl
  let cA: class A


  assert |- ( A e. RR -> -e A e. RR )

  proof
    cA
    cr
    wcel
    cA
    cxne
    cA
    cneg
    cr
    cA
    rexneg
    cA
    renegcl
    eqeltrd
end
