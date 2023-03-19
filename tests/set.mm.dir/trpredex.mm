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
include "df-trpred.mm"
include "wfn.mm"
include "wcel.mm"
include "frfnom.mm"
include "omex.mm"
include "fnex.mm"
include "mp2an.mm"
include "rnex.mm"
include "uniex.mm"
include "eqeltri.mm"

theorem trpredex
  let cA: class A
  let cR: class R
  let cX: class X
  let va: setvar a
  let vy: setvar y


  assert |- TrPred ( R , A , X ) e. _V

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
    #
    cuni
    cvv
    vy
    cA
    cR
    cX
    va
    df-trpred
    @3
    @2
    @2
    com
    wfn
    com
    cvv
    wcel
    @2
    cvv
    wcel
    @1
    @0
    frfnom
    omex
    com
    cvv
    @2
    fnex
    mp2an
    rnex
    uniex
    eqeltri
end
