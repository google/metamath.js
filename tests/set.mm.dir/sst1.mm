include "ct1.mm"
include "t1top.mm"
include "cid.mm"
include "cres.mm"
include "cnt1.mm"
include "sshauslem.mm"

theorem sst1
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


  assert |- ( ( J e. Fre /\ K e. ( TopOn ` X ) /\ J C_ K ) -> K e. Fre )

  proof
    ct1
    cJ
    cK
    cX
    t1sep.1
    cJ
    t1top
    cid
    cX
    cres
    cK
    cJ
    cX
    cX
    cnt1
    sshauslem
end
