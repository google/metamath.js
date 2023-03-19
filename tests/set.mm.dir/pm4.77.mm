include "wo.mm"
include "wi.mm"
include "wa.mm"
include "jaob.mm"
include "bicomi.mm"

theorem pm4.77
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ps -> ph ) /\ ( ch -> ph ) ) <-> ( ( ps \/ ch ) -> ph ) )

  proof
    wps
    wch
    wo
    wph
    wi
    wps
    wph
    wi
    wch
    wph
    wi
    wa
    wps
    wph
    wch
    jaob
    bicomi
end
