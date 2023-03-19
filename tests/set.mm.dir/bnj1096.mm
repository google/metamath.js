include "w-bnj17.mm"
include "ax-5.mm"
include "bnj982.mm"
include "hbxfrbi.mm"

theorem bnj1096
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  assume bnj1096.1: |- ( ph -> A. x ph )
  assume bnj1096.2: |- ( ps <-> ( ch /\ th /\ ta /\ ph ) )

  disjoint ch x
  disjoint ta x
  disjoint th x
  assert |- ( ps -> A. x ps )

  proof
    wps
    wch
    wth
    wta
    wph
    w-bnj17
    vx
    bnj1096.2
    wch
    wth
    wta
    wph
    vx
    wch
    vx
    ax-5
    wth
    vx
    ax-5
    wta
    vx
    ax-5
    bnj1096.1
    bnj982
    hbxfrbi
end
