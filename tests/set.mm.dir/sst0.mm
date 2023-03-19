include "ct0.mm"
include "t0top.mm"
include "cid.mm"
include "cres.mm"
include "cnt0.mm"
include "sshauslem.mm"

theorem sst0
  let cJ: class J
  let cK: class K
  let cX: class X
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume t1sep.1: |- X = U. J


  assert |- ( ( J e. Kol2 /\ K e. ( TopOn ` X ) /\ J C_ K ) -> K e. Kol2 )

  proof
    ct0
    cJ
    cK
    cX
    t1sep.1
    cJ
    t0top
    cid
    cX
    cres
    cK
    cJ
    cX
    cX
    cnt0
    sshauslem
end
