include "wn.mm"
include "id.mm"
include "pm2.21.mm"
include "mt4d.mm"

theorem notnotrALT
  let wph: wff ph


  assert |- ( -. -. ph -> ph )

  proof
    wph
    wn
    #
    wn
    #
    @1
    wph
    @1
    id
    @0
    @1
    wn
    pm2.21
    mt4d
end
