include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wb.mm"
include "dedlema.mm"
include "dedlemb.mm"
include "pm2.61i.mm"

theorem pm4.42
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph <-> ( ( ph /\ ps ) \/ ( ph /\ -. ps ) ) )

  proof
    wps
    wph
    wph
    wps
    wa
    wph
    wps
    wn
    wa
    wo
    wb
    wps
    wph
    wph
    dedlema
    wps
    wph
    wph
    dedlemb
    pm2.61i
end
