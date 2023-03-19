include "wi.mm"
include "tbw-ax2.mm"
include "tbw-ax1.mm"
include "tbwsyl.mm"
include "tbw-ax3.mm"
include "mpsyl.mm"

theorem tbwlem1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) )

  proof
    wps
    wps
    wch
    wi
    #
    wch
    wi
    #
    wi
    wph
    @0
    wi
    @1
    wph
    wch
    wi
    #
    wi
    wps
    @2
    wi
    wps
    @0
    @1
    wi
    #
    @1
    wps
    @0
    wps
    wi
    @3
    wps
    @0
    tbw-ax2
    @0
    wps
    wch
    tbw-ax1
    tbwsyl
    @3
    @1
    wch
    wi
    @1
    wi
    @1
    @0
    @1
    wch
    tbw-ax1
    @1
    wch
    tbw-ax3
    tbwsyl
    tbwsyl
    wph
    @0
    wch
    tbw-ax1
    wps
    @1
    @2
    tbw-ax1
    mpsyl
end
