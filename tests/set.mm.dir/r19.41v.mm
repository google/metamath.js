include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "anass.mm"
include "exbii.mm"
include "19.41v.mm"
include "bitr3i.mm"
include "df-rex.mm"
include "anbi1i.mm"
include "3bitr4i.mm"

theorem r19.41v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint ps x
  assert |- ( E. x e. A ( ph /\ ps ) <-> ( E. x e. A ph /\ ps ) )

  proof
    vx
    cv
    cA
    wcel
    #
    wph
    wps
    wa
    #
    wa
    #
    vx
    wex
    #
    @0
    wph
    wa
    #
    vx
    wex
    #
    wps
    wa
    #
    @1
    vx
    cA
    wrex
    wph
    vx
    cA
    wrex
    #
    wps
    wa
    @3
    @4
    wps
    wa
    #
    vx
    wex
    @6
    @8
    @2
    vx
    @0
    wph
    wps
    anass
    exbii
    @4
    wps
    vx
    19.41v
    bitr3i
    @1
    vx
    cA
    df-rex
    @7
    @5
    wps
    wph
    vx
    cA
    df-rex
    anbi1i
    3bitr4i
end
