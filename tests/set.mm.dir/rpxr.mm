include "crp.mm"
include "wcel.mm"
include "rpre.mm"
include "rexrd.mm"

theorem rpxr
  let cA: class A


  assert |- ( A e. RR+ -> A e. RR* )

  proof
    cA
    crp
    wcel
    cA
    cA
    rpre
    rexrd
end
