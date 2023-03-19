include "w-bnj17.mm"
include "wa.mm"
include "w3a.mm"
include "bnj248.mm"
include "df-3an.mm"
include "bitr4i.mm"

theorem bnj253
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ( ph /\ ps ) /\ ch /\ th ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wps
    wa
    #
    wch
    wa
    wth
    wa
    @0
    wch
    wth
    w3a
    wph
    wps
    wch
    wth
    bnj248
    @0
    wch
    wth
    df-3an
    bitr4i
end
