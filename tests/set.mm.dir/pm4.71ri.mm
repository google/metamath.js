include "wi.mm"
include "wa.mm"
include "wb.mm"
include "pm4.71r.mm"
include "mpbi.mm"

theorem pm4.71ri
  let wph: wff ph
  let wps: wff ps
  assume pm4.71ri.1: |- ( ph -> ps )


  assert |- ( ph <-> ( ps /\ ph ) )

  proof
    wph
    wps
    wi
    wph
    wps
    wph
    wa
    wb
    pm4.71ri.1
    wph
    wps
    pm4.71r
    mpbi
end
