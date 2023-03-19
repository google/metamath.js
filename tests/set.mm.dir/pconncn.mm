include "cpconn.mm"
include "wcel.mm"
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
include "wral.mm"
include "ctop.mm"
include "ispconn.mm"
include "simprbi.mm"
include "eqeq2.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "anbi2d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem pconncn
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vj: setvar j
  assume ispconn.1: |- X = U. J

  disjoint A f
  disjoint B f
  disjoint J f
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint f j
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint J x
  disjoint J y
  disjoint X j
  disjoint X x
  disjoint X y
  assert |- ( ( J e. PConn /\ A e. X /\ B e. X ) -> E. f e. ( II Cn J ) ( ( f ` 0 ) = A /\ ( f ` 1 ) = B ) )

  proof
    cJ
    cpconn
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cc0
    vf
    cv
    #
    cfv
    #
    cA
    wceq
    #
    c1
    @3
    cfv
    #
    cB
    wceq
    #
    wa
    #
    vf
    cii
    cJ
    ccn
    co
    #
    wrex
    #
    @0
    @4
    vx
    cv
    #
    wceq
    #
    @6
    vy
    cv
    #
    wceq
    #
    wa
    #
    vf
    @9
    wrex
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @1
    @2
    wa
    @10
    @0
    cJ
    ctop
    wcel
    @17
    vx
    vy
    vf
    cJ
    cX
    ispconn.1
    ispconn
    simprbi
    @16
    @10
    @5
    @14
    wa
    #
    vf
    @9
    wrex
    vx
    vy
    cA
    cB
    cX
    cX
    @11
    cA
    wceq
    #
    @15
    @18
    vf
    @9
    @19
    @12
    @5
    @14
    @11
    cA
    @4
    eqeq2
    anbi1d
    rexbidv
    @13
    cB
    wceq
    #
    @18
    @8
    vf
    @9
    @20
    @14
    @7
    @5
    @13
    cB
    @6
    eqeq2
    anbi2d
    rexbidv
    rspc2v
    syl5com
    3impib
end
