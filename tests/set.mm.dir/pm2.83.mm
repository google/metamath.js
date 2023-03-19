include "wi.mm"
include "imim1.mm"
include "imim3i.mm"

theorem pm2.83
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ( ch -> th ) ) -> ( ph -> ( ps -> th ) ) ) )

  proof
    wps
    wch
    wi
    wch
    wth
    wi
    wps
    wth
    wi
    wph
    wps
    wch
    wth
    imim1
    imim3i
end
