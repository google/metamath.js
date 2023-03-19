include "wi.mm"
include "ax-1.mm"
include "syl6.mm"

theorem a1dd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume a1dd.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps -> ( th -> ch ) ) )

  proof
    wph
    wps
    wch
    wth
    wch
    wi
    a1dd.1
    wch
    wth
    ax-1
    syl6
end
