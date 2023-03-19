include "wn.mm"
include "id.mm"
include "ja.mm"

theorem pm2.01
  let wph: wff ph


  assert |- ( ( ph -> -. ph ) -> -. ph )

  proof
    wph
    wph
    wn
    #
    @0
    @0
    id
    #
    @1
    ja
end
