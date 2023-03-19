include "wo.mm"
include "orcom.mm"
include "orbi2i.mm"
include "3bitri.mm"

theorem orbi1i
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume orbi2i.1: |- ( ph <-> ps )


  assert |- ( ( ph \/ ch ) <-> ( ps \/ ch ) )

  proof
    wph
    wch
    wo
    wch
    wph
    wo
    wch
    wps
    wo
    wps
    wch
    wo
    wph
    wch
    orcom
    wph
    wps
    wch
    orbi2i.1
    orbi2i
    wch
    wps
    orcom
    3bitri
end
