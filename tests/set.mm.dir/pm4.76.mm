include "wa.mm"
include "wi.mm"
include "jcab.mm"
include "bicomi.mm"

theorem pm4.76
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) <-> ( ph -> ( ps /\ ch ) ) )

  proof
    wph
    wps
    wch
    wa
    wi
    wph
    wps
    wi
    wph
    wch
    wi
    wa
    wph
    wps
    wch
    jcab
    bicomi
end
