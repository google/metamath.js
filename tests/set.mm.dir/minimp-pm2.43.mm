include "wi.mm"
include "minimp-ax2.mm"
include "minimp-ax1.mm"
include "ax-mp.mm"
include "mp2.mm"

theorem minimp-pm2.43
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) )

  proof
    wph
    wph
    wps
    wi
    #
    wi
    #
    wph
    wph
    wi
    #
    @0
    wi
    wi
    @1
    @2
    wi
    #
    @1
    @0
    wi
    wph
    wph
    wps
    minimp-ax2
    wph
    @0
    wph
    wi
    wi
    @3
    wph
    @0
    minimp-ax1
    wph
    @0
    wph
    minimp-ax2
    ax-mp
    @1
    @2
    @0
    minimp-ax2
    mp2
end
