include "wfal.mm"
include "wi.mm"
include "tbw-ax4.mm"
include "tbw-ax1.mm"
include "tbwlem1.mm"
include "ax-mp.mm"
include "mpsyl.mm"
include "tbwsyl.mm"

theorem tbwlem2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> F. ) ) -> ( ( ( ph -> ch ) -> th ) -> ( ps -> th ) ) )

  proof
    wph
    wps
    wfal
    wi
    #
    wi
    #
    wps
    wph
    wch
    wi
    #
    wi
    #
    @2
    wth
    wi
    wps
    wth
    wi
    wi
    wps
    @0
    wch
    wi
    #
    wi
    #
    @1
    @4
    @2
    wi
    @3
    @0
    wps
    wch
    wi
    #
    wi
    #
    @5
    wfal
    wch
    wi
    #
    @7
    wch
    tbw-ax4
    @0
    @8
    @6
    wi
    wi
    @8
    @7
    wi
    wps
    wfal
    wch
    tbw-ax1
    @0
    @8
    @6
    tbwlem1
    ax-mp
    ax-mp
    @0
    wps
    wch
    tbwlem1
    ax-mp
    wph
    @0
    wch
    tbw-ax1
    wps
    @4
    @2
    tbw-ax1
    mpsyl
    wps
    @2
    wth
    tbw-ax1
    tbwsyl
end
