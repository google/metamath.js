include "wn.mm"
include "wo.mm"
include "olc.mm"
include "imori.mm"
include "a1i.mm"

theorem tsor3
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( -. ps \/ ( ph \/ ps ) ) )

  proof
    wps
    wn
    wph
    wps
    wo
    #
    wo
    wth
    wps
    @0
    wps
    wph
    olc
    imori
    a1i
end
