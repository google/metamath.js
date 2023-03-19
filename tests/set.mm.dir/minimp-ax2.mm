include "wi.mm"
include "minimp-ax2c.mm"
include "minimp-sylsimp.mm"
include "ax-mp.mm"
include "mp2.mm"

theorem minimp-ax2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )

  proof
    wph
    wps
    wi
    #
    wph
    wps
    wch
    wi
    wi
    #
    wph
    wch
    wi
    #
    wi
    wi
    #
    @1
    @3
    @0
    @2
    wi
    #
    wi
    #
    wi
    #
    @1
    @4
    wi
    #
    wph
    wps
    wch
    minimp-ax2c
    @0
    @1
    wi
    @5
    wi
    @6
    @0
    @1
    @2
    minimp-ax2c
    @0
    @1
    @5
    minimp-sylsimp
    ax-mp
    @1
    @3
    wi
    @6
    @7
    wi
    #
    wi
    @3
    @8
    wi
    @1
    @3
    @4
    minimp-ax2c
    @1
    @3
    @8
    minimp-sylsimp
    ax-mp
    mp2
end
