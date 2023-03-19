include "w3a.mm"
include "bnj1275.mm"
include "bnj1198.mm"

theorem bnj1345
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  assume bnj1345.1: |- ( ph -> E. x ( ps /\ ch ) )
  assume bnj1345.2: |- ( th <-> ( ph /\ ps /\ ch ) )
  assume bnj1345.3: |- ( ph -> A. x ph )


  assert |- ( ph -> E. x th )

  proof
    wph
    wph
    wps
    wch
    w3a
    vx
    wth
    wph
    wps
    wch
    vx
    bnj1345.1
    bnj1345.3
    bnj1275
    bnj1345.2
    bnj1198
end
