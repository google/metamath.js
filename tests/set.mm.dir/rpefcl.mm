include "cr.mm"
include "wcel.mm"
include "ce.mm"
include "cfv.mm"
include "reefcl.mm"
include "efgt0.mm"
include "elrpd.mm"

theorem rpefcl
  let cA: class A


  assert |- ( A e. RR -> ( exp ` A ) e. RR+ )

  proof
    cA
    cr
    wcel
    cA
    ce
    cfv
    cA
    reefcl
    cA
    efgt0
    elrpd
end
