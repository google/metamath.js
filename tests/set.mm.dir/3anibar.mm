include "w3a.mm"
include "simp3.mm"
include "mpbirand.mm"

theorem 3anibar
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3anibar.1: |- ( ( ph /\ ps /\ ch ) -> ( th <-> ( ch /\ ta ) ) )


  assert |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) )

  proof
    wph
    wps
    wch
    w3a
    wth
    wch
    wta
    wph
    wps
    wch
    simp3
    3anibar.1
    mpbirand
end
