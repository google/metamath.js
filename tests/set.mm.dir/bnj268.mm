include "w3a.mm"
include "wa.mm"
include "w-bnj17.mm"
include "3ancomb.mm"
include "anbi1i.mm"
include "df-bnj17.mm"
include "3bitr4i.mm"

theorem bnj268
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ch /\ th ) <-> ( ph /\ ch /\ ps /\ th ) )

  proof
    wph
    wps
    wch
    w3a
    #
    wth
    wa
    wph
    wch
    wps
    w3a
    #
    wth
    wa
    wph
    wps
    wch
    wth
    w-bnj17
    wph
    wch
    wps
    wth
    w-bnj17
    @0
    @1
    wth
    wph
    wps
    wch
    3ancomb
    anbi1i
    wph
    wps
    wch
    wth
    df-bnj17
    wph
    wch
    wps
    wth
    df-bnj17
    3bitr4i
end
