include "a1i.mm"
include "mpdi.mm"

theorem mpii
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpii.1: |- ch
  assume mpii.2: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    wch
    wps
    mpii.1
    a1i
    mpii.2
    mpdi
end
