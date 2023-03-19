include "ccl.mm"
include "cfv.mm"
include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "clsidm.mm"
include "mp2an.mm"
include "fveq1i.mm"
include "fveq12i.mm"
include "3eqtr4i.mm"

theorem kur14lem5
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


  assert |- ( K ` ( K ` A ) ) = ( K ` A )

  proof
    cA
    cJ
    ccl
    cfv
    #
    cfv
    #
    @0
    cfv
    #
    @1
    cA
    cK
    cfv
    #
    cK
    cfv
    @3
    cJ
    ctop
    wcel
    cA
    cX
    wss
    @2
    @1
    wceq
    kur14lem.j
    kur14lem.a
    cA
    cJ
    cX
    kur14lem.x
    clsidm
    mp2an
    @3
    @1
    cK
    @0
    kur14lem.k
    cA
    cK
    @0
    kur14lem.k
    fveq1i
    #
    fveq12i
    @4
    3eqtr4i
end
