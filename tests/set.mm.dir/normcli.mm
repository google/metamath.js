include "chil.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "cr.mm"
include "normcl.mm"
include "ax-mp.mm"

theorem normcli
  let cA: class A
  assume normcl.1: |- A e. ~H


  assert |- ( normh ` A ) e. RR

  proof
    cA
    chil
    wcel
    cA
    cno
    cfv
    cr
    wcel
    normcl.1
    cA
    normcl
    ax-mp
end
