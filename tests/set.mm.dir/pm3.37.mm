include "wa.mm"
include "wi.mm"
include "wn.mm"
include "pm4.14.mm"
include "biimpi.mm"

theorem pm3.37
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) -> ch ) -> ( ( ph /\ -. ch ) -> -. ps ) )

  proof
    wph
    wps
    wa
    wch
    wi
    wph
    wch
    wn
    wa
    wps
    wn
    wi
    wph
    wps
    wch
    pm4.14
    biimpi
end
