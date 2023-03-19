include "wn.mm"
include "wi.mm"
include "pm2.21.mm"
include "a2i.mm"
include "con4d.mm"
include "pm2.43i.mm"

theorem pm2.18
  param wph: wff ph


  assert |- ( ( -. ph -> ph ) -> ph )

  proof
    wph
    wn
    #
    wph
    wi
    #
    wph
    @1
    wph
    @1
    @0
    wph
    @1
    wn
    #
    wph
    @2
    pm2.21
    a2i
    con4d
    pm2.43i
end
