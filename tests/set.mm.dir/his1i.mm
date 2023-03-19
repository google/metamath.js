include "chil.mm"
include "wcel.mm"
include "csp.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "ax-his1.mm"
include "mp2an.mm"

theorem his1i
  let cA: class A
  let cB: class B
  assume his1.1: |- A e. ~H
  assume his1.2: |- B e. ~H


  assert |- ( A .ih B ) = ( * ` ( B .ih A ) )

  proof
    cA
    chil
    wcel
    cB
    chil
    wcel
    cA
    cB
    csp
    co
    cB
    cA
    csp
    co
    ccj
    cfv
    wceq
    his1.1
    his1.2
    cA
    cB
    ax-his1
    mp2an
end
