include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wrex.mm"
include "cuni.mm"
include "wral.mm"
include "ctop.mm"
include "cpconn.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "oveq2.mm"
include "rexeqdv.mm"
include "raleqbidv.mm"
include "df-pconn.mm"
include "elrab2.mm"

theorem ispconn
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cJ: class J
  let cX: class X
  let cA: class A
  let cB: class B
  let vj: setvar j
  assume ispconn.1: |- X = U. J

  disjoint f x
  disjoint f y
  disjoint x y
  disjoint J f
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint A f
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B y
  disjoint f j
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint X j
  assert |- ( J e. PConn <-> ( J e. Top /\ A. x e. X A. y e. X E. f e. ( II Cn J ) ( ( f ` 0 ) = x /\ ( f ` 1 ) = y ) ) )

  proof
    cc0
    vf
    cv
    #
    cfv
    vx
    cv
    wceq
    c1
    @0
    cfv
    vy
    cv
    wceq
    wa
    #
    vf
    cii
    vj
    cv
    #
    ccn
    co
    #
    wrex
    #
    vy
    @2
    cuni
    #
    wral
    #
    vx
    @5
    wral
    @1
    vf
    cii
    cJ
    ccn
    co
    #
    wrex
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    vj
    cJ
    ctop
    cpconn
    @2
    cJ
    wceq
    #
    @6
    @9
    vx
    @5
    cX
    @10
    @5
    cJ
    cuni
    cX
    @2
    cJ
    unieq
    ispconn.1
    syl6eqr
    #
    @10
    @4
    @8
    vy
    @5
    cX
    @11
    @10
    @1
    vf
    @3
    @7
    @2
    cJ
    cii
    ccn
    oveq2
    rexeqdv
    raleqbidv
    raleqbidv
    vx
    vy
    vf
    vj
    df-pconn
    elrab2
end
