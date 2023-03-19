include "wn.mm"
include "wi.mm"
include "idn1.mm"
include "pm2.21.mm"
include "e1a.mm"
include "con4.mm"
include "id.mm"
include "e11.mm"
include "in1.mm"

theorem notnotrALTVD
  let wph: wff ph


  assert |- ( -. -. ph -> ph )

  proof
    wph
    wn
    #
    wn
    #
    wph
    @1
    @1
    wph
    wi
    #
    @1
    wph
    @1
    @0
    @1
    wn
    #
    wi
    #
    @2
    @1
    @1
    @4
    @1
    idn1
    #
    @0
    @3
    pm2.21
    e1a
    wph
    @1
    con4
    e1a
    @5
    @2
    id
    e11
    in1
end
