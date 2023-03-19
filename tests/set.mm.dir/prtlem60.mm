include "wi.mm"
include "a1i.mm"
include "syldd.mm"

theorem prtlem60
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume prtlem60.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume prtlem60.2: |- ( ps -> ( th -> ta ) )


  assert |- ( ph -> ( ps -> ( ch -> ta ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    prtlem60.1
    wps
    wth
    wta
    wi
    wi
    wph
    prtlem60.2
    a1i
    syldd
end
