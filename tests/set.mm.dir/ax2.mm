include "wi.mm"
include "luklem7.mm"
include "luklem8.mm"
include "luklem6.mm"
include "ax-mp.mm"
include "luklem1.mm"

theorem ax2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )

  proof
    wph
    wps
    wch
    wi
    wi
    wps
    wph
    wch
    wi
    #
    wi
    #
    wph
    wps
    wi
    #
    @0
    wi
    #
    wph
    wps
    wch
    luklem7
    @1
    @2
    wph
    @0
    wi
    #
    wi
    #
    @3
    wps
    @0
    wph
    luklem8
    @4
    @0
    wi
    @5
    @3
    wi
    wph
    wch
    luklem6
    @4
    @0
    @2
    luklem8
    ax-mp
    luklem1
    luklem1
end
