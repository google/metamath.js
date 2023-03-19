include "wo.mm"
include "orcom.mm"
include "sylib.mm"

theorem orcomd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
