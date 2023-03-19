include "chil.mm"
include "cr.mm"
include "cno.mm"
include "normf.mm"
include "ffvelrni.mm"

theorem normcl
  let cA: class A


  assert |- ( A e. ~H -> ( normh ` A ) e. RR )

  proof
    chil
    cr
    cA
    cno
    normf
    ffvelrni
end
