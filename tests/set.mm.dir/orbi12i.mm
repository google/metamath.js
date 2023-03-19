include "wo.mm"
include "orbi2i.mm"
include "orbi1i.mm"
include "bitri.mm"

theorem orbi12i
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume orbi12i.1: |- ( ph <-> ps )
  assume orbi12i.2: |- ( ch <-> th )


  assert |- ( ( ph \/ ch ) <-> ( ps \/ th ) )

  proof
    wph
    wch
    wo
    wph
    wth
    wo
    wps
    wth
    wo
    wch
    wth
    wph
    orbi12i.2
    orbi2i
    wph
    wps
    wth
    orbi12i.1
    orbi1i
    bitri
end
