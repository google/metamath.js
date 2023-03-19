include "cnt.mm"
include "cfv.mm"
include "cdif.mm"
include "ccl.mm"
include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "ntrval2.mm"
include "mp2an.mm"
include "fveq1i.mm"
include "difeq2i.mm"
include "3eqtr4i.mm"

theorem kur14lem2
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


  assert |- ( I ` A ) = ( X \ ( K ` ( X \ A ) ) )

  proof
    cA
    cJ
    cnt
    cfv
    #
    cfv
    #
    cX
    cX
    cA
    cdif
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    cdif
    #
    cA
    cI
    cfv
    cX
    @2
    cK
    cfv
    #
    cdif
    cJ
    ctop
    wcel
    cA
    cX
    wss
    @1
    @5
    wceq
    kur14lem.j
    kur14lem.a
    cA
    cJ
    cX
    kur14lem.x
    ntrval2
    mp2an
    cA
    cI
    @0
    kur14lem.i
    fveq1i
    @6
    @4
    cX
    @2
    cK
    @3
    kur14lem.k
    fveq1i
    difeq2i
    3eqtr4i
end
