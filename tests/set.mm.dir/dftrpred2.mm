include "ctrpred.mm"
include "cvv.mm"
include "cv.mm"
include "cpred.mm"
include "ciun.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "df-trpred.mm"
include "wfn.mm"
include "wceq.mm"
include "frfnom.mm"
include "fniunfv.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem dftrpred2
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vi: setvar i
  let cX: class X
  let va: setvar a

  disjoint R a
  disjoint R i
  disjoint R y
  disjoint a i
  disjoint a y
  disjoint i y
  disjoint A a
  disjoint A i
  disjoint A y
  disjoint X a
  disjoint X i
  disjoint X y
  assert |- TrPred ( R , A , X ) = U_ i e. _om ( ( rec ( ( a e. _V |-> U_ y e. a Pred ( R , A , y ) ) , Pred ( R , A , X ) ) |` _om ) ` i )

  proof
    cA
    cR
    cX
    ctrpred
    va
    cvv
    vy
    va
    cv
    cA
    cR
    vy
    cv
    cpred
    ciun
    cmpt
    #
    cA
    cR
    cX
    cpred
    #
    crdg
    com
    cres
    #
    crn
    cuni
    #
    vi
    com
    vi
    cv
    @2
    cfv
    ciun
    #
    vy
    cA
    cR
    cX
    va
    df-trpred
    @2
    com
    wfn
    @4
    @3
    wceq
    @1
    @0
    frfnom
    vi
    com
    @2
    fniunfv
    ax-mp
    eqtr4i
end
