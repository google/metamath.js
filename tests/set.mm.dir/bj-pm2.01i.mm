include "wn.mm"
include "wi.mm"
include "pm2.01.mm"
include "ax-mp.mm"

theorem bj-pm2.01i
  let wph: wff ph
  assume bj-pm2.01i.1: |- ( ph -> -. ph )


  assert |- -. ph

  proof
    wph
    wph
    wn
    #
    wi
    @0
    bj-pm2.01i.1
    wph
    pm2.01
    ax-mp
end
