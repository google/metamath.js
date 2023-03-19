include "wn.mm"
include "wl-id.mm"
include "wl-con1i.mm"

theorem wl-notnotr
  let wph: wff ph


  assert |- ( -. -. ph -> ph )

  proof
    wph
    wph
    wn
    #
    @0
    wl-id
    wl-con1i
end
