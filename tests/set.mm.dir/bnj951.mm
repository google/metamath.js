include "w3a.mm"
include "w-bnj17.mm"
include "3jca.mm"
include "df-bnj17.mm"
include "sylanbrc.mm"

theorem bnj951
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume bnj951.1: |- ( ta -> ph )
  assume bnj951.2: |- ( ta -> ps )
  assume bnj951.3: |- ( ta -> ch )
  assume bnj951.4: |- ( ta -> th )


  assert |- ( ta -> ( ph /\ ps /\ ch /\ th ) )

  proof
    wta
    wph
    wps
    wch
    w3a
    wth
    wph
    wps
    wch
    wth
    w-bnj17
    wta
    wph
    wps
    wch
    bnj951.1
    bnj951.2
    bnj951.3
    3jca
    bnj951.4
    wph
    wps
    wch
    wth
    df-bnj17
    sylanbrc
end
