include "crngo.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "cablo.mm"
include "cxp.mm"
include "wf.mm"
include "w3a.mm"
include "rngoi.mm"
include "simprrd.mm"
include "r19.12.mm"
include "syl.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "oveq1.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "rspccva.mm"
include "sylan.mm"

theorem rngoid
  let vu: setvar u
  let cA: class A
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  assume ringi.1: |- G = ( 1st ` R )
  assume ringi.2: |- H = ( 2nd ` R )
  assume ringi.3: |- X = ran G

  disjoint G u
  disjoint H u
  disjoint X u
  disjoint A u
  disjoint R u
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint R x
  assert |- ( ( R e. RingOps /\ A e. X ) -> E. u e. X ( ( u H A ) = A /\ ( A H u ) = A ) )

  proof
    cR
    crngo
    wcel
    #
    vu
    cv
    #
    vx
    cv
    #
    cH
    co
    #
    @2
    wceq
    #
    @2
    @1
    cH
    co
    #
    @2
    wceq
    #
    wa
    #
    vu
    cX
    wrex
    #
    vx
    cX
    wral
    #
    cA
    cX
    wcel
    @1
    cA
    cH
    co
    #
    cA
    wceq
    #
    cA
    @1
    cH
    co
    #
    cA
    wceq
    #
    wa
    #
    vu
    cX
    wrex
    #
    @0
    @7
    vx
    cX
    wral
    vu
    cX
    wrex
    #
    @9
    @0
    cG
    cablo
    wcel
    cX
    cX
    cxp
    cX
    cH
    wf
    wa
    @3
    vy
    cv
    #
    cH
    co
    @1
    @2
    @17
    cH
    co
    #
    cH
    co
    wceq
    @1
    @2
    @17
    cG
    co
    cH
    co
    @3
    @1
    @17
    cH
    co
    #
    cG
    co
    wceq
    @1
    @2
    cG
    co
    @17
    cH
    co
    @19
    @18
    cG
    co
    wceq
    w3a
    vy
    cX
    wral
    vx
    cX
    wral
    vu
    cX
    wral
    @16
    vu
    vx
    vy
    cR
    cG
    cH
    cX
    ringi.1
    ringi.2
    ringi.3
    rngoi
    simprrd
    @7
    vu
    vx
    cX
    cX
    r19.12
    syl
    @8
    @15
    vx
    cA
    cX
    @2
    cA
    wceq
    #
    @7
    @14
    vu
    cX
    @20
    @4
    @11
    @6
    @13
    @20
    @3
    @10
    @2
    cA
    @2
    cA
    @1
    cH
    oveq2
    @20
    id
    #
    eqeq12d
    @20
    @5
    @12
    @2
    cA
    @2
    cA
    @1
    cH
    oveq1
    @21
    eqeq12d
    anbi12d
    rexbidv
    rspccva
    sylan
end
