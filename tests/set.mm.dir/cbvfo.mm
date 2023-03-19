include "wfo.mm"
include "crn.mm"
include "wral.mm"
include "wfn.mm"
include "wb.mm"
include "fofn.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "bicomd.mm"
include "eqcoms.mm"
include "ralrn.mm"
include "syl.mm"
include "forn.mm"
include "raleqdv.mm"
include "bitr3d.mm"

theorem cbvfo
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  assume cbvfo.1: |- ( ( F ` x ) = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint ph y
  disjoint ps x
  assert |- ( F : A -onto-> B -> ( A. x e. A ph <-> A. y e. B ps ) )

  proof
    cA
    cB
    cF
    wfo
    #
    wps
    vy
    cF
    crn
    #
    wral
    #
    wph
    vx
    cA
    wral
    #
    wps
    vy
    cB
    wral
    @0
    cF
    cA
    wfn
    @2
    @3
    wb
    cA
    cB
    cF
    fofn
    wps
    wph
    vy
    vx
    cA
    cF
    wps
    wph
    wb
    vx
    cv
    cF
    cfv
    #
    vy
    cv
    #
    @4
    @5
    wceq
    wph
    wps
    cbvfo.1
    bicomd
    eqcoms
    ralrn
    syl
    @0
    wps
    vy
    @1
    cB
    cA
    cB
    cF
    forn
    raleqdv
    bitr3d
end
