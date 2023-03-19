include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "cxp.mm"
include "ciun.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "iunss.mm"
include "wcel.mm"
include "snssi.mm"
include "fvssunirn.mm"
include "xpss12.mm"
include "sylancl.mm"
include "mprgbir.mm"
include "eqsstri.mm"

theorem marypha2lem1
  let vx: setvar x
  let cA: class A
  let cT: class T
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cX: class X
  assume marypha2lem.t: |- T = U_ x e. A ( { x } X. ( F ` x ) )

  disjoint A x
  disjoint F x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint X x
  disjoint X y
  assert |- T C_ ( A X. U. ran F )

  proof
    cT
    vx
    cA
    vx
    cv
    #
    csn
    #
    @0
    cF
    cfv
    #
    cxp
    #
    ciun
    #
    cA
    cF
    crn
    cuni
    #
    cxp
    #
    marypha2lem.t
    @4
    @6
    wss
    @3
    @6
    wss
    #
    vx
    cA
    vx
    cA
    @3
    @6
    iunss
    @0
    cA
    wcel
    @1
    cA
    wss
    @2
    @5
    wss
    @7
    @0
    cA
    snssi
    cF
    @0
    fvssunirn
    @1
    cA
    @2
    @5
    xpss12
    sylancl
    mprgbir
    eqsstri
end
