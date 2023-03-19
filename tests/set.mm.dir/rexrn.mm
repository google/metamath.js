include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "crn.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "fvexd.mm"
include "wceq.mm"
include "wrex.mm"
include "fvelrnb.mm"
include "eqcom.mm"
include "rexbii.mm"
include "syl6bb.mm"
include "wb.mm"
include "adantl.mm"
include "rexxfr2d.mm"

theorem rexrn
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  assume rexrn.1: |- ( x = ( F ` y ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint ps x
  disjoint ph y
  assert |- ( F Fn A -> ( E. x e. ran F ph <-> E. y e. A ps ) )

  proof
    cF
    cA
    wfn
    #
    wph
    wps
    vx
    vy
    vy
    cv
    #
    cF
    cfv
    #
    cF
    crn
    #
    cA
    cvv
    @0
    @1
    cA
    wcel
    wa
    @1
    cF
    fvexd
    @0
    vx
    cv
    #
    @3
    wcel
    @2
    @4
    wceq
    #
    vy
    cA
    wrex
    @4
    @2
    wceq
    #
    vy
    cA
    wrex
    vy
    cA
    @4
    cF
    fvelrnb
    @5
    @6
    vy
    cA
    @2
    @4
    eqcom
    rexbii
    syl6bb
    @6
    wph
    wps
    wb
    @0
    rexrn.1
    adantl
    rexxfr2d
end
