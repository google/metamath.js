include "wi.mm"
include "wa.mm"
include "wb.mm"
include "pm4.71.mm"
include "mpbi.mm"

theorem pm4.71i
  param wph: wff ph
  param wps: wff ps
  assume pm4.71i.1: |- ( ph -> ps )


  assert |- ( ph <-> ( ph /\ ps ) )

  proof
    wph
    wps
    wi
    wph
    wph
    wps
    wa
    wb
    pm4.71i.1
    wph
    wps
    pm4.71
    mpbi
end
