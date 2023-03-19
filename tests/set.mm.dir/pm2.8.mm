include "wo.mm"
include "wn.mm"
include "pm2.53.mm"
include "con1d.mm"
include "orim1d.mm"

theorem pm2.8
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ps ) -> ( ( -. ps \/ ch ) -> ( ph \/ ch ) ) )

  proof
    wph
    wps
    wo
    #
    wps
    wn
    wph
    wch
    @0
    wph
    wps
    wph
    wps
    pm2.53
    con1d
    orim1d
end
