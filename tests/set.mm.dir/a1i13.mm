include "wi.mm"
include "a1d.mm"
include "a1i.mm"

theorem a1i13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume a1i13.1: |- ( ps -> th )


  assert |- ( ph -> ( ps -> ( ch -> th ) ) )

  proof
    wps
    wch
    wth
    wi
    wi
    wph
    wps
    wth
    wch
    a1i13.1
    a1d
    a1i
end
