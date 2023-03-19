include "wi.mm"
include "wa.mm"
include "wb.mm"
include "pm4.71.mm"
include "sylib.mm"

theorem pm4.71d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm4.71rd.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps <-> ( ps /\ ch ) ) )

  proof
    wph
    wps
    wch
    wi
    wps
    wps
    wch
    wa
    wb
    pm4.71rd.1
    wps
    wch
    pm4.71
    sylib
end
