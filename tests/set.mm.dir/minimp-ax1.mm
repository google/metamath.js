include "wi.mm"
include "minimp-sylsimp.mm"
include "ax-mp.mm"

theorem minimp-ax1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps -> ph ) )

  proof
    wph
    wps
    wi
    #
    wph
    wi
    wps
    wph
    wi
    #
    wi
    wph
    @1
    wi
    wph
    wps
    wph
    minimp-sylsimp
    @0
    wph
    @1
    minimp-sylsimp
    ax-mp
end
