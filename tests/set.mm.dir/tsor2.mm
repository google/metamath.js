include "wn.mm"
include "wo.mm"
include "orc.mm"
include "imori.mm"
include "a1i.mm"

theorem tsor2
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( -. ph \/ ( ph \/ ps ) ) )

  proof
    wph
    wn
    wph
    wps
    wo
    #
    wo
    wth
    wph
    @0
    wph
    wps
    orc
    imori
    a1i
end
