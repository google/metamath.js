include "cha.mm"
include "wcel.mm"
include "ct1.mm"
include "csn.mm"
include "ccld.mm"
include "cfv.mm"
include "haust1.mm"
include "t1sncld.mm"
include "sylan.mm"

theorem sncld
  let cP: class P
  let cJ: class J
  let cX: class X
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume t1sep.1: |- X = U. J


  assert |- ( ( J e. Haus /\ P e. X ) -> { P } e. ( Clsd ` J ) )

  proof
    cJ
    cha
    wcel
    cJ
    ct1
    wcel
    cP
    cX
    wcel
    cP
    csn
    cJ
    ccld
    cfv
    wcel
    cJ
    haust1
    cP
    cJ
    cX
    t1sep.1
    t1sncld
    sylan
end
