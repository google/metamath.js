include "wa.mm"
include "wn.mm"
include "wi.mm"
include "df-an.mm"
include "bicomi.mm"

theorem pm4.63
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph -> -. ps ) <-> ( ph /\ ps ) )

  proof
    wph
    wps
    wa
    wph
    wps
    wn
    wi
    wn
    wph
    wps
    df-an
    bicomi
end
