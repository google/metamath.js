include "cfv.mm"
include "cdif.mm"
include "cnt.mm"
include "ctp.mm"
include "cun.mm"
include "cpr.mm"
include "eqid.mm"
include "kur14lem9.mm"

theorem kur14lem10
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cJ: class J
  let cK: class K
  let cX: class X
  assume kur14lem10.j: |- J e. Top
  assume kur14lem10.x: |- X = U. J
  assume kur14lem10.k: |- K = ( cls ` J )
  assume kur14lem10.s: |- S = |^| { x e. ~P ~P X | ( A e. x /\ A. y e. x { ( X \ y ) , ( K ` y ) } C_ x ) }
  assume kur14lem10.a: |- A C_ X

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint X x
  disjoint X y
  assert |- ( S e. Fin /\ ( # ` S ) <_ ; 1 4 )

  proof
    vx
    vy
    cA
    cX
    cA
    cK
    cfv
    #
    cdif
    #
    cX
    cA
    cdif
    #
    cK
    cfv
    #
    @0
    cJ
    cnt
    cfv
    #
    cfv
    #
    cS
    cA
    @2
    @0
    ctp
    @1
    @3
    cA
    @4
    cfv
    #
    ctp
    cun
    @1
    cK
    cfv
    #
    @5
    @6
    cK
    cfv
    #
    ctp
    cun
    @3
    @4
    cfv
    #
    @5
    cK
    cfv
    @7
    @4
    cfv
    ctp
    @9
    cK
    cfv
    @8
    @4
    cfv
    cpr
    cun
    cun
    #
    @4
    cJ
    cK
    cX
    kur14lem10.j
    kur14lem10.x
    kur14lem10.k
    @4
    eqid
    kur14lem10.a
    @1
    eqid
    @3
    eqid
    @5
    eqid
    @10
    eqid
    kur14lem10.s
    kur14lem9
end
