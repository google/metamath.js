include "a1i.mm"
include "mpand.mm"

theorem mpani
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpani.1: |- ps
  assume mpani.2: |- ( ph -> ( ( ps /\ ch ) -> th ) )


  assert |- ( ph -> ( ch -> th ) )

  proof
    wph
    wps
    wch
    wth
    wps
    wph
    mpani.1
    a1i
    mpani.2
    mpand
end
