include "wo.mm"
include "wn.mm"
include "pm2.53.mm"
include "idd.mm"
include "jaod.mm"

theorem pm2.63
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/ ps ) -> ( ( -. ph \/ ps ) -> ps ) )

  proof
    wph
    wps
    wo
    #
    wph
    wn
    wps
    wps
    wph
    wps
    pm2.53
    @0
    wps
    idd
    jaod
end
