include "cha.mm"
include "haustop.mm"
include "cid.mm"
include "cres.mm"
include "cnhaus.mm"
include "sshauslem.mm"

theorem sshaus
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


  assert |- ( ( J e. Haus /\ K e. ( TopOn ` X ) /\ J C_ K ) -> K e. Haus )

  proof
    cha
    cJ
    cK
    cX
    t1sep.1
    cJ
    haustop
    cid
    cX
    cres
    cK
    cJ
    cX
    cX
    cnhaus
    sshauslem
end
