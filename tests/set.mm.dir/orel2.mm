include "wn.mm"
include "idd.mm"
include "pm2.21.mm"
include "jaod.mm"

theorem orel2
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ph -> ( ( ps \/ ph ) -> ps ) )

  proof
    wph
    wn
    #
    wps
    wps
    wph
    @0
    wps
    idd
    wph
    wps
    pm2.21
    jaod
end
