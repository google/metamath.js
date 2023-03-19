include "wn.mm"
include "wo.mm"
include "pm2.46.mm"
include "con1i.mm"
include "orri.mm"

theorem rb-ax3
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ph \/ ( ps \/ ph ) )

  proof
    wph
    wn
    #
    wps
    wph
    wo
    #
    @1
    @0
    wps
    wph
    pm2.46
    con1i
    orri
end
