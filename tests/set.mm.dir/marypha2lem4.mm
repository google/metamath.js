include "wfn.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "cuni.mm"
include "wcel.mm"
include "copab.mm"
include "cres.mm"
include "crn.mm"
include "marypha2lem2.mm"
include "imaeq1i.mm"
include "df-ima.mm"
include "eqtri.mm"
include "wceq.mm"
include "resopab2.mm"
include "adantl.mm"
include "rneqd.mm"
include "wex.mm"
include "cab.mm"
include "rnopab.mm"
include "wrex.mm"
include "df-rex.mm"
include "bicomi.mm"
include "abbii.mm"
include "df-iun.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "wfun.mm"
include "fnfun.mm"
include "adantr.mm"
include "funiunfv.mm"
include "syl.mm"

theorem marypha2lem4
  let vx: setvar x
  let cA: class A
  let cT: class T
  let cF: class F
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  assume marypha2lem.t: |- T = U_ x e. A ( { x } X. ( F ` x ) )

  disjoint A x
  disjoint F x
  disjoint X x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint X y
  assert |- ( ( F Fn A /\ X C_ A ) -> ( T " X ) = U. ( F " X ) )

  proof
    cF
    cA
    wfn
    #
    cX
    cA
    wss
    #
    wa
    #
    cT
    cX
    cima
    #
    vx
    cX
    vx
    cv
    #
    cF
    cfv
    #
    ciun
    #
    cF
    cX
    cima
    cuni
    #
    @2
    @3
    @4
    cA
    wcel
    vy
    cv
    @5
    wcel
    #
    wa
    vx
    vy
    copab
    #
    cX
    cres
    #
    crn
    #
    @6
    @3
    @9
    cX
    cima
    @11
    cT
    @9
    cX
    vx
    vy
    cA
    cT
    cF
    marypha2lem.t
    marypha2lem2
    imaeq1i
    @9
    cX
    df-ima
    eqtri
    @2
    @11
    @4
    cX
    wcel
    @8
    wa
    #
    vx
    vy
    copab
    #
    crn
    #
    @6
    @2
    @10
    @13
    @1
    @10
    @13
    wceq
    @0
    @8
    vx
    vy
    cX
    cA
    resopab2
    adantl
    rneqd
    @2
    @14
    @12
    vx
    wex
    #
    vy
    cab
    #
    @6
    @12
    vx
    vy
    rnopab
    @16
    @6
    wceq
    @2
    @16
    @8
    vx
    cX
    wrex
    #
    vy
    cab
    @6
    @15
    @17
    vy
    @17
    @15
    @8
    vx
    cX
    df-rex
    bicomi
    abbii
    vx
    vy
    cX
    @5
    df-iun
    eqtr4i
    a1i
    syl5eq
    eqtrd
    syl5eq
    @2
    cF
    wfun
    #
    @6
    @7
    wceq
    @0
    @18
    @1
    cA
    cF
    fnfun
    adantr
    vx
    cX
    cF
    funiunfv
    syl
    eqtrd
end
