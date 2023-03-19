include "wi.mm"
include "a1d.mm"
include "a2d.mm"

theorem imim2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume imim2d.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) )

  proof
    wph
    wth
    wps
    wch
    wph
    wps
    wch
    wi
    wth
    imim2d.1
    a1d
    a2d
end
