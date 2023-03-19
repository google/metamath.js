include "cv.mm"
include "csn.mm"
include "cpw.mm"
include "cxp.mm"
include "ciun.mm"
include "ccrd.mm"
include "cfv.mm"
include "com.mm"
include "cfn.mm"
include "cin.mm"
include "wceq.mm"
include "iuneq1.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"

theorem ackbij1lem7
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cG: class G
  let cH: class H
  let cB: class B
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G x
  disjoint G y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B x
  disjoint B y
  assert |- ( A e. ( ~P _om i^i Fin ) -> ( F ` A ) = ( card ` U_ y e. A ( { y } X. ~P y ) ) )

  proof
    vx
    cA
    vy
    vx
    cv
    #
    vy
    cv
    #
    csn
    @1
    cpw
    cxp
    #
    ciun
    #
    ccrd
    cfv
    vy
    cA
    @2
    ciun
    #
    ccrd
    cfv
    com
    cpw
    cfn
    cin
    cF
    @0
    cA
    wceq
    @3
    @4
    ccrd
    vy
    @0
    cA
    @2
    iuneq1
    fveq2d
    ackbij.f
    @4
    ccrd
    fvex
    fvmpt
end
