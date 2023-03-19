include "wn.mm"
include "wa.mm"
include "wi.mm"
include "annim.mm"
include "bicomi.mm"

theorem pm4.61
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph -> ps ) <-> ( ph /\ -. ps ) )

  proof
    wph
    wps
    wn
    wa
    wph
    wps
    wi
    wn
    wph
    wps
    annim
    bicomi
end
