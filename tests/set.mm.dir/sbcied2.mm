include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "id.mm"
include "sylan9eqr.mm"
include "syldan.mm"
include "sbcied.mm"

theorem sbcied2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume sbcied2.1: |- ( ph -> A e. V )
  assume sbcied2.2: |- ( ph -> A = B )
  assume sbcied2.3: |- ( ( ph /\ x = B ) -> ( ps <-> ch ) )

  disjoint A x
  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( [. A / x ]. ps <-> ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    cV
    sbcied2.1
    wph
    vx
    cv
    #
    cA
    wceq
    #
    @0
    cB
    wceq
    wps
    wch
    wb
    @1
    wph
    @0
    cA
    cB
    @1
    id
    sbcied2.2
    sylan9eqr
    sbcied2.3
    syldan
    sbcied
end
