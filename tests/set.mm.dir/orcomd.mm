include "wo.mm"
include "orcom.mm"
include "sylib.mm"

theorem orcomd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume orcomd.1: |- ( ph -> ( ps \/ ch ) )


  assert |- ( ph -> ( ch \/ ps ) )

  proof
    wph
    wps
    wch
    wo
    wch
    wps
    wo
    orcomd.1
    wps
    wch
    orcom
    sylib
end
