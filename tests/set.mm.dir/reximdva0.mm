include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wrex.mm"
include "n0.mm"
include "ex.mm"
include "ancld.mm"
include "eximdv.mm"
include "imp.mm"
include "sylan2b.mm"
include "df-rex.mm"
include "sylibr.mm"

theorem reximdva0
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume reximdva0.1: |- ( ( ph /\ x e. A ) -> ps )

  disjoint A x
  disjoint ph x
  assert |- ( ( ph /\ A =/= (/) ) -> E. x e. A ps )

  proof
    wph
    cA
    c0
    wne
    #
    wa
    vx
    cv
    cA
    wcel
    #
    wps
    wa
    #
    vx
    wex
    #
    wps
    vx
    cA
    wrex
    @0
    wph
    @1
    vx
    wex
    #
    @3
    vx
    cA
    n0
    wph
    @4
    @3
    wph
    @1
    @2
    vx
    wph
    @1
    wps
    wph
    @1
    wps
    reximdva0.1
    ex
    ancld
    eximdv
    imp
    sylan2b
    wps
    vx
    cA
    df-rex
    sylibr
end
