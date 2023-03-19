include "wo.mm"
include "orbi1d.mm"
include "orbi2d.mm"
include "bitrd.mm"

theorem orbi12d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume bi12d.1: |- ( ph -> ( ps <-> ch ) )
  assume bi12d.2: |- ( ph -> ( th <-> ta ) )


  assert |- ( ph -> ( ( ps \/ th ) <-> ( ch \/ ta ) ) )

  proof
    wph
    wps
    wth
    wo
    wch
    wth
    wo
    wch
    wta
    wo
    wph
    wps
    wch
    wth
    bi12d.1
    orbi1d
    wph
    wth
    wta
    wch
    bi12d.2
    orbi2d
    bitrd
end
