include "w-bnj17.mm"
include "w3a.mm"
include "wa.mm"
include "df-bnj17.mm"
include "df-3an.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem bnj248
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ( ( ph /\ ps ) /\ ch ) /\ th ) )

  proof
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wps
    wch
    w3a
    #
    wth
    wa
    wph
    wps
    wa
    wch
    wa
    #
    wth
    wa
    wph
    wps
    wch
    wth
    df-bnj17
    @0
    @1
    wth
    wph
    wps
    wch
    df-3an
    anbi1i
    bitri
end
