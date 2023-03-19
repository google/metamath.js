include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cicc.mm"
include "cv.mm"
include "cmin.mm"
include "cmpt.mm"
include "ctopon.mm"
include "iitopon.mm"
include "a1i.mm"
include "iirevcn.mm"
include "id.mm"
include "cnmpt11f.mm"
include "syl5eqel.mm"
include "0elunit.mm"
include "oveq2.mm"
include "1m0e1.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "mp1i.mm"
include "1elunit.mm"
include "1m1e0.mm"
include "3jca.mm"

theorem pcorevcl
  let vx: setvar x
  let cF: class F
  let cG: class G
  let cJ: class J
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  let cH: class H
  let cP: class P
  assume pcorev.1: |- G = ( x e. ( 0 [,] 1 ) |-> ( F ` ( 1 - x ) ) )

  disjoint F x
  disjoint J x
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint t x
  disjoint t y
  disjoint F t
  disjoint x y
  disjoint F y
  disjoint G s
  disjoint G t
  disjoint G y
  disjoint H y
  disjoint J s
  disjoint J t
  disjoint J y
  disjoint P s
  disjoint P t
  disjoint P x
  disjoint P y
  assert |- ( F e. ( II Cn J ) -> ( G e. ( II Cn J ) /\ ( G ` 0 ) = ( F ` 1 ) /\ ( G ` 1 ) = ( F ` 0 ) ) )

  proof
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    cG
    @0
    wcel
    cc0
    cG
    cfv
    c1
    cF
    cfv
    #
    wceq
    #
    c1
    cG
    cfv
    cc0
    cF
    cfv
    #
    wceq
    #
    @1
    cG
    vx
    cc0
    c1
    cicc
    co
    #
    c1
    vx
    cv
    #
    cmin
    co
    #
    cF
    cfv
    #
    cmpt
    @0
    pcorev.1
    @1
    vx
    @8
    cF
    cii
    cii
    cJ
    @6
    cii
    @6
    ctopon
    cfv
    wcel
    @1
    iitopon
    a1i
    vx
    @6
    @8
    cmpt
    cii
    cii
    ccn
    co
    wcel
    @1
    vx
    iirevcn
    a1i
    @1
    id
    cnmpt11f
    syl5eqel
    cc0
    @6
    wcel
    @3
    @1
    0elunit
    vx
    cc0
    @9
    @2
    @6
    cG
    @7
    cc0
    wceq
    #
    @8
    c1
    cF
    @10
    @8
    c1
    cc0
    cmin
    co
    c1
    @7
    cc0
    c1
    cmin
    oveq2
    1m0e1
    syl6eq
    fveq2d
    pcorev.1
    c1
    cF
    fvex
    fvmpt
    mp1i
    c1
    @6
    wcel
    @5
    @1
    1elunit
    vx
    c1
    @9
    @4
    @6
    cG
    @7
    c1
    wceq
    #
    @8
    cc0
    cF
    @11
    @8
    c1
    c1
    cmin
    co
    cc0
    @7
    c1
    c1
    cmin
    oveq2
    1m1e0
    syl6eq
    fveq2d
    pcorev.1
    cc0
    cF
    fvex
    fvmpt
    mp1i
    3jca
end
