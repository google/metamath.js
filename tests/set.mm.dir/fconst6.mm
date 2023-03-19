include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "fconst6g.mm"
include "ax-mp.mm"

theorem fconst6
  let cA: class A
  let cB: class B
  let cC: class C
  assume fconst6.1: |- B e. C


  assert |- ( A X. { B } ) : A --> C

  proof
    cB
    cC
    wcel
    cA
    cC
    cA
    cB
    csn
    cxp
    wf
    fconst6.1
    cA
    cB
    cC
    fconst6g
    ax-mp
end
