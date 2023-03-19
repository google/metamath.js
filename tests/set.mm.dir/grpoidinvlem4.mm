include "cgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "grpoass.mm"
include "syl13anc.mm"
include "oveq2.mm"
include "sylan9eq.mm"
include "oveq1.mm"
include "sylan9req.mm"
include "anasss.mm"
include "r19.29an.mm"

theorem grpoidinvlem4
  let vy: setvar y
  let cA: class A
  let cU: class U
  let cG: class G
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  let cB: class B
  let cC: class C
  let vu: setvar u
  assume grpfo.1: |- X = ran G

  disjoint A y
  disjoint G y
  disjoint X y
  disjoint U y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint G w
  disjoint G x
  disjoint G z
  disjoint X u
  disjoint X w
  disjoint X x
  disjoint X z
  assert |- ( ( ( G e. GrpOp /\ A e. X ) /\ E. y e. X ( ( y G A ) = U /\ ( A G y ) = U ) ) -> ( A G U ) = ( U G A ) )

  proof
    cG
    cgr
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    vy
    cv
    #
    cA
    cG
    co
    #
    cU
    wceq
    #
    cA
    @3
    cG
    co
    #
    cU
    wceq
    #
    wa
    cA
    cU
    cG
    co
    #
    cU
    cA
    cG
    co
    #
    wceq
    #
    vy
    cX
    @2
    @3
    cX
    wcel
    #
    wa
    #
    @5
    @7
    @10
    @12
    @5
    wa
    @7
    @8
    @6
    cA
    cG
    co
    #
    @9
    @12
    @5
    @13
    cA
    @4
    cG
    co
    #
    @8
    @12
    @0
    @1
    @11
    @1
    @13
    @14
    wceq
    @0
    @1
    @11
    simpll
    @0
    @1
    @11
    simplr
    #
    @2
    @11
    simpr
    @15
    cA
    @3
    cA
    cG
    cX
    grpfo.1
    grpoass
    syl13anc
    @4
    cU
    cA
    cG
    oveq2
    sylan9eq
    @6
    cU
    cA
    cG
    oveq1
    sylan9req
    anasss
    r19.29an
end
