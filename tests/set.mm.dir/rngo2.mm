include "crngo.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "rngoid.mm"
include "oveq12.mm"
include "anidms.mm"
include "eqcomd.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr.mm"
include "rngodir.mm"
include "syl13anc.mm"
include "eqeq2d.mm"
include "syl5ibr.mm"
include "adantrd.mm"
include "reximdva.mm"
include "mpd.mm"

theorem rngo2
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  assume ringi.1: |- G = ( 1st ` R )
  assume ringi.2: |- H = ( 2nd ` R )
  assume ringi.3: |- X = ran G

  disjoint G x
  disjoint H x
  disjoint X x
  disjoint A x
  disjoint R x
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint H u
  disjoint H y
  disjoint H z
  disjoint X u
  disjoint X y
  disjoint X z
  disjoint A u
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint R u
  assert |- ( ( R e. RingOps /\ A e. X ) -> E. x e. X ( A G A ) = ( ( x G x ) H A ) )

  proof
    cR
    crngo
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    vx
    cv
    #
    cA
    cH
    co
    #
    cA
    wceq
    #
    cA
    @3
    cH
    co
    cA
    wceq
    #
    wa
    #
    vx
    cX
    wrex
    cA
    cA
    cG
    co
    #
    @3
    @3
    cG
    co
    cA
    cH
    co
    #
    wceq
    #
    vx
    cX
    wrex
    vx
    cA
    cR
    cG
    cH
    cX
    ringi.1
    ringi.2
    ringi.3
    rngoid
    @2
    @7
    @10
    vx
    cX
    @2
    @3
    cX
    wcel
    #
    wa
    #
    @5
    @10
    @6
    @5
    @10
    @12
    @8
    @4
    @4
    cG
    co
    #
    wceq
    @5
    @13
    @8
    @5
    @13
    @8
    wceq
    @4
    cA
    @4
    cA
    cG
    oveq12
    anidms
    eqcomd
    @12
    @9
    @13
    @8
    @12
    @0
    @11
    @11
    @1
    @9
    @13
    wceq
    @0
    @1
    @11
    simpll
    @2
    @11
    simpr
    #
    @14
    @0
    @1
    @11
    simplr
    @3
    @3
    cA
    cR
    cG
    cH
    cX
    ringi.1
    ringi.2
    ringi.3
    rngodir
    syl13anc
    eqeq2d
    syl5ibr
    adantrd
    reximdva
    mpd
end
