include "wn.mm"
include "wi.mm"
include "wo.mm"
include "ax-1.mm"
include "imori.mm"
include "a1i.mm"

theorem tsim3
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( -. ps \/ ( ph -> ps ) ) )

  proof
    wps
    wn
    wph
    wps
    wi
    #
    wo
    wth
    wps
    @0
    wps
    wph
    ax-1
    imori
    a1i
end
