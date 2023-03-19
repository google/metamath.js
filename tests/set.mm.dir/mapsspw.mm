include "cmap.mm"
include "co.mm"
include "cpm.mm"
include "cxp.mm"
include "cpw.mm"
include "mapsspm.mm"
include "pmsspw.mm"
include "sstri.mm"

theorem mapsspw
  let cA: class A
  let cB: class B
  let vf: setvar f


  assert |- ( A ^m B ) C_ ~P ( B X. A )

  proof
    cA
    cB
    cmap
    co
    cA
    cB
    cpm
    co
    cB
    cA
    cxp
    cpw
    cA
    cB
    mapsspm
    cA
    cB
    pmsspw
    sstri
end
