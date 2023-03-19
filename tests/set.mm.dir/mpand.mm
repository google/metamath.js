include "ancomsd.mm"
include "mpan2d.mm"

theorem mpand
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpand.1: |- ( ph -> ps )
  assume mpand.2: |- ( ph -> ( ( ps /\ ch ) -> th ) )


  assert |- ( ph -> ( ch -> th ) )

  proof
    wph
    wch
    wps
    wth
    mpand.1
    wph
    wps
    wch
    wth
    mpand.2
    ancomsd
    mpan2d
end
