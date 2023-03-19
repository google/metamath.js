include "wi.mm"
include "ax-1.mm"
include "syl6.mm"

theorem a1dd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
