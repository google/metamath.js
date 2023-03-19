include "w3a.mm"
include "hb3an.mm"
include "hbxfrbi.mm"

theorem bnj1276
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  assume bnj1276.1: |- ( ph -> A. x ph )
  assume bnj1276.2: |- ( ps -> A. x ps )
  assume bnj1276.3: |- ( ch -> A. x ch )
  assume bnj1276.4: |- ( th <-> ( ph /\ ps /\ ch ) )


  assert |- ( th -> A. x th )

  proof
    wth
    wph
    wps
    wch
    w3a
    vx
    bnj1276.4
    wph
    wps
    wch
    vx
    bnj1276.1
    bnj1276.2
    bnj1276.3
    hb3an
    hbxfrbi
end
