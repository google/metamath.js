include "wi.mm"
include "a1d.mm"

theorem 2a1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 2a1d.1: |- ( ph -> ps )


  assert |- ( ph -> ( ch -> ( th -> ps ) ) )

  proof
    wph
    wth
    wps
    wi
    wch
    wph
    wps
    wth
    2a1d.1
    a1d
    a1d
end
