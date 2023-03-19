include "wn.mm"
include "wo.mm"
include "olc.mm"
include "orel1.mm"
include "impbid2.mm"

theorem biorf
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ph -> ( ps <-> ( ph \/ ps ) ) )

  proof
    wph
    wn
    wps
    wph
    wps
    wo
    wps
    wph
    olc
    wph
    wps
    orel1
    impbid2
end
