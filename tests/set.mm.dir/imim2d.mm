include "wi.mm"
include "a1d.mm"
include "a2d.mm"

theorem imim2d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
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
