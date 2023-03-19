include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cvv.mm"
include "fvexd.mm"
include "wa.mm"
include "wb.mm"
include "simpr.mm"
include "fveq2.mm"
include "syl6reqr.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "syl.mm"
include "bicomd.mm"
include "sbcied.mm"

theorem sbcies
  let wph: wff ph
  let wps: wff ps
  let vw: setvar w
  let cA: class A
  let cE: class E
  let cW: class W
  let va: setvar a
  assume sbcies.a: |- A = ( E ` W )
  assume sbcies.1: |- ( a = A -> ( ph <-> ps ) )

  disjoint a w
  disjoint E a
  disjoint W a
  disjoint a ph
  assert |- ( w = W -> ( [. ( E ` w ) / a ]. ps <-> ph ) )

  proof
    vw
    cv
    #
    cW
    wceq
    #
    wps
    wph
    va
    @0
    cE
    cfv
    #
    cvv
    @1
    @0
    cE
    fvexd
    @1
    va
    cv
    #
    @2
    wceq
    #
    wa
    #
    wph
    wps
    @5
    @3
    cA
    wceq
    wph
    wps
    wb
    @5
    @3
    @2
    cA
    @1
    @4
    simpr
    @1
    cA
    @2
    wceq
    @4
    @1
    @2
    cW
    cE
    cfv
    cA
    @0
    cW
    cE
    fveq2
    sbcies.a
    syl6reqr
    adantr
    eqtr4d
    sbcies.1
    syl
    bicomd
    sbcied
end
