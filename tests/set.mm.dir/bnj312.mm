include "w3a.mm"
include "wa.mm"
include "w-bnj17.mm"
include "3ancoma.mm"
include "anbi1i.mm"
include "df-bnj17.mm"
include "3bitr4i.mm"

theorem bnj312
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ps /\ ph /\ ch /\ th ) )

  proof
    wph
    wps
    wch
    w3a
    #
    wth
    wa
    wps
    wph
    wch
    w3a
    #
    wth
    wa
    wph
    wps
    wch
    wth
    w-bnj17
    wps
    wph
    wch
    wth
    w-bnj17
    @0
    @1
    wth
    wph
    wps
    wch
    3ancoma
    anbi1i
    wph
    wps
    wch
    wth
    df-bnj17
    wps
    wph
    wch
    wth
    df-bnj17
    3bitr4i
end
