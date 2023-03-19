include "cr.mm"
include "cc.mm"
include "ax-resscn.mm"
include "sseli.mm"

theorem recn
  let cA: class A


  assert |- ( A e. RR -> A e. CC )

  proof
    cr
    cc
    cA
    ax-resscn
    sseli
end
