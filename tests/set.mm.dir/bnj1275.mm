include "wa.mm"
include "w3a.mm"
include "bnj596.mm"
include "3anass.mm"
include "bnj1198.mm"

theorem bnj1275
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bnj1275.1: |- ( ph -> E. x ( ps /\ ch ) )
  assume bnj1275.2: |- ( ph -> A. x ph )


  assert |- ( ph -> E. x ( ph /\ ps /\ ch ) )

  proof
    wph
    wph
    wps
    wch
    wa
    #
    wa
    vx
    wph
    wps
    wch
    w3a
    wph
    @0
    vx
    bnj1275.2
    bnj1275.1
    bnj596
    wph
    wps
    wch
    3anass
    bnj1198
end
