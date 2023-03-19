include "chil.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0v.mm"
include "wb.mm"
include "norm-i.mm"
include "ax-mp.mm"

theorem norm-i-i
  let cA: class A
  assume normcl.1: |- A e. ~H


  assert |- ( ( normh ` A ) = 0 <-> A = 0h )

  proof
    cA
    chil
    wcel
    cA
    cno
    cfv
    cc0
    wceq
    cA
    c0v
    wceq
    wb
    normcl.1
    cA
    norm-i
    ax-mp
end
