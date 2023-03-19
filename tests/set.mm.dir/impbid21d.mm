include "wi.mm"
include "a1i.mm"
include "a1d.mm"
include "impbidd.mm"

theorem impbid21d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume impbid21d.1: |- ( ps -> ( ch -> th ) )
  assume impbid21d.2: |- ( ph -> ( th -> ch ) )


  assert |- ( ph -> ( ps -> ( ch <-> th ) ) )

  proof
    wph
    wps
    wch
    wth
    wps
    wch
    wth
    wi
    wi
    wph
    impbid21d.1
    a1i
    wph
    wth
    wch
    wi
    wps
    impbid21d.2
    a1d
    impbidd
end
