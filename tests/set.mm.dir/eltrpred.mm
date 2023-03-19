include "ctrpred.mm"
include "wcel.mm"
include "com.mm"
include "cv.mm"
include "cvv.mm"
include "cpred.mm"
include "ciun.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "cfv.mm"
include "wrex.mm"
include "dftrpred2.mm"
include "eleq2i.mm"
include "eliun.mm"
include "bitri.mm"

theorem eltrpred
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vi: setvar i
  let cX: class X
  let cY: class Y
  let va: setvar a

  disjoint R a
  disjoint R y
  disjoint R i
  disjoint a y
  disjoint a i
  disjoint i y
  disjoint A a
  disjoint A y
  disjoint A i
  disjoint X a
  disjoint X y
  disjoint X i
  disjoint Y a
  disjoint Y y
  disjoint Y i
  assert |- ( Y e. TrPred ( R , A , X ) <-> E. i e. _om Y e. ( ( rec ( ( a e. _V |-> U_ y e. a Pred ( R , A , y ) ) , Pred ( R , A , X ) ) |` _om ) ` i ) )

  proof
    cY
    cA
    cR
    cX
    ctrpred
    #
    wcel
    cY
    vi
    com
    vi
    cv
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
    cA
    cR
    cX
    cpred
    crdg
    com
    cres
    cfv
    #
    ciun
    #
    wcel
    cY
    @1
    wcel
    vi
    com
    wrex
    @0
    @2
    cY
    vy
    cA
    cR
    vi
    cX
    va
    dftrpred2
    eleq2i
    vi
    cY
    com
    @1
    eliun
    bitri
end
