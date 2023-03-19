include "wi.mm"
include "wn.mm"
include "ax-1.mm"
include "con3i.mm"
include "a1d.mm"

theorem pm2.51
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph -> ps ) -> ( ph -> -. ps ) )

  proof
    wph
    wps
    wi
    #
    wn
    wps
    wn
    wph
    wps
    @0
    wps
    wph
    ax-1
    con3i
    a1d
end
