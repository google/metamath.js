include "c0.mm"
include "csn.mm"
include "wss.mm"
include "wdisj.mm"
include "0ss.mm"
include "disjxsn.mm"
include "disjss1.mm"
include "mp2.mm"

theorem disjx0
  let vx: setvar x
  let cB: class B
  let vy: setvar y
  let cA: class A


  assert |- Disj_ x e. (/) B

  proof
    c0
    c0
    csn
    #
    wss
    vx
    @0
    cB
    wdisj
    vx
    c0
    cB
    wdisj
    @0
    0ss
    vx
    c0
    cB
    disjxsn
    vx
    c0
    @0
    cB
    disjss1
    mp2
end
