include "wo.mm"
include "orbi2d.mm"
include "orcom.mm"
include "3bitr4g.mm"

theorem orbi1d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
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
