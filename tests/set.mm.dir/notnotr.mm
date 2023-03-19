include "wn.mm"
include "pm2.21.mm"
include "pm2.18d.mm"

theorem notnotr
  param wph: wff ph


  assert |- ( -. -. ph -> ph )

  proof
    wph
    wn
    #
    wn
    wph
    @0
    wph
    pm2.21
    pm2.18d
end
