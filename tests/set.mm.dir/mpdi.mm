include "wi.mm"
include "a1i.mm"
include "mpdd.mm"

theorem mpdi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpdi.1: |- ( ps -> ch )
  assume mpdi.2: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    wps
    wch
    wi
    wph
    mpdi.1
    a1i
    mpdi.2
    mpdd
end
