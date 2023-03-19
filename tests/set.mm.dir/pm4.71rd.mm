include "wi.mm"
include "wa.mm"
include "wb.mm"
include "pm4.71r.mm"
include "sylib.mm"

theorem pm4.71rd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm4.71rd.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps <-> ( ch /\ ps ) ) )

  proof
    wph
    wps
    wch
    wi
    wps
    wch
    wps
    wa
    wb
    pm4.71rd.1
    wps
    wch
    pm4.71r
    sylib
end
