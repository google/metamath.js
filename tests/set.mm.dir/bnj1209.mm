include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "bnj1196.mm"
include "ancli.mm"
include "19.42v.mm"
include "sylibr.mm"
include "w3a.mm"
include "3anass.mm"
include "bitri.mm"
include "bnj1198.mm"

theorem bnj1209
  let wph: wff ph
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let cB: class B
  assume bnj1209.1: |- ( ch -> E. x e. B ph )
  assume bnj1209.2: |- ( th <-> ( ch /\ x e. B /\ ph ) )

  disjoint ch x
  assert |- ( ch -> E. x th )

  proof
    wch
    wch
    vx
    cv
    cB
    wcel
    #
    wph
    wa
    #
    wa
    #
    vx
    wth
    wch
    wch
    @1
    vx
    wex
    #
    wa
    @2
    vx
    wex
    wch
    @3
    wch
    wph
    vx
    cB
    bnj1209.1
    bnj1196
    ancli
    wch
    @1
    vx
    19.42v
    sylibr
    wth
    wch
    @0
    wph
    w3a
    @2
    bnj1209.2
    wch
    @0
    wph
    3anass
    bitri
    bnj1198
end
