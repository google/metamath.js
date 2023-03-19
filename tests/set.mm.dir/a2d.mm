include "wi.mm"
include "ax-2.mm"
include "syl.mm"

theorem a2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume a2d.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) )

  proof
    wph
    wps
    wch
    wth
    wi
    wi
    wps
    wch
    wi
    wps
    wth
    wi
    wi
    a2d.1
    wps
    wch
    wth
    ax-2
    syl
end
