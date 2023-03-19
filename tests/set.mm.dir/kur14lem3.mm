include "cfv.mm"
include "ccl.mm"
include "fveq1i.mm"
include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "clsss3.mm"
include "mp2an.mm"
include "eqsstri.mm"

theorem kur14lem3
  let cA: class A
  let cI: class I
  let cJ: class J
  let cK: class K
  let cX: class X
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  assume kur14lem.j: |- J e. Top
  assume kur14lem.x: |- X = U. J
  assume kur14lem.k: |- K = ( cls ` J )
  assume kur14lem.i: |- I = ( int ` J )
  assume kur14lem.a: |- A C_ X


  assert |- ( K ` A ) C_ X

  proof
    cA
    cK
    cfv
    cA
    cJ
    ccl
    cfv
    #
    cfv
    #
    cX
    cA
    cK
    @0
    kur14lem.k
    fveq1i
    cJ
    ctop
    wcel
    cA
    cX
    wss
    @1
    cX
    wss
    kur14lem.j
    kur14lem.a
    cA
    cJ
    cX
    kur14lem.x
    clsss3
    mp2an
    eqsstri
end
