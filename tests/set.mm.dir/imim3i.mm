include "wi.mm"
include "imim2i.mm"
include "a2d.mm"

theorem imim3i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume imim3i.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ( th -> ph ) -> ( ( th -> ps ) -> ( th -> ch ) ) )

  proof
    wth
    wph
    wi
    wth
    wps
    wch
    wph
    wps
    wch
    wi
    wth
    imim3i.1
    imim2i
    a2d
end
