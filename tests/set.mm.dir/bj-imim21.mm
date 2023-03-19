include "wi.mm"
include "imim1.mm"
include "imim2d.mm"

theorem bj-imim21
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ps ) -> ( ( ch -> ( ps -> th ) ) -> ( ch -> ( ph -> th ) ) ) )

  proof
    wph
    wps
    wi
    wps
    wth
    wi
    wph
    wth
    wi
    wch
    wph
    wps
    wth
    imim1
    imim2d
end
