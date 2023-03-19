include "w-bnj17.mm"
include "wa.mm"
include "w3a.mm"
include "bnj250.mm"
include "df-3an.mm"
include "anbi2i.mm"
include "bitr4i.mm"

theorem bnj252
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ph /\ ( ps /\ ch /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wps
    wch
    wa
    wth
    wa
    #
    wa
    wph
    wps
    wch
    wth
    w3a
    #
    wa
    wph
    wps
    wch
    wth
    bnj250
    @1
    @0
    wph
    wps
    wch
    wth
    df-3an
    anbi2i
    bitr4i
end
