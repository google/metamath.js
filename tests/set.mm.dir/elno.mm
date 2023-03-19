include "csur.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "wf.mm"
include "con0.mm"
include "wrex.mm"
include "elex.mm"
include "fex.mm"
include "ancoms.mm"
include "rexlimiva.mm"
include "wceq.mm"
include "feq1.mm"
include "rexbidv.mm"
include "df-no.mm"
include "elab2g.mm"
include "pm5.21nii.mm"

theorem elno
  let vx: setvar x
  let cA: class A
  let vf: setvar f

  disjoint A x
  disjoint A f
  disjoint f x
  assert |- ( A e. No <-> E. x e. On A : x --> { 1o , 2o } )

  proof
    cA
    csur
    wcel
    cA
    cvv
    wcel
    #
    vx
    cv
    #
    c1o
    c2o
    cpr
    #
    cA
    wf
    #
    vx
    con0
    wrex
    #
    cA
    csur
    elex
    @3
    @0
    vx
    con0
    @3
    @1
    con0
    wcel
    @0
    @1
    @2
    con0
    cA
    fex
    ancoms
    rexlimiva
    @1
    @2
    vf
    cv
    #
    wf
    #
    vx
    con0
    wrex
    @4
    vf
    cA
    csur
    cvv
    @5
    cA
    wceq
    @6
    @3
    vx
    con0
    @1
    @2
    @5
    cA
    feq1
    rexbidv
    vf
    vx
    df-no
    elab2g
    pm5.21nii
end
