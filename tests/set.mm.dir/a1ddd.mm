include "wi.mm"
include "ax-1.mm"
include "syl8.mm"

theorem a1ddd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume a1ddd.1: |- ( ph -> ( ps -> ( ch -> ta ) ) )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )

  proof
    wph
    wps
    wch
    wta
    wth
    wta
    wi
    a1ddd.1
    wta
    wth
    ax-1
    syl8
end
