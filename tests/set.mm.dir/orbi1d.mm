include "wo.mm"
include "orbi2d.mm"
include "orcom.mm"
include "3bitr4g.mm"

theorem orbi1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bid.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ th ) ) )

  proof
    wph
    wth
    wps
    wo
    wth
    wch
    wo
    wps
    wth
    wo
    wch
    wth
    wo
    wph
    wps
    wch
    wth
    bid.1
    orbi2d
    wps
    wth
    orcom
    wch
    wth
    orcom
    3bitr4g
end
