include "wn.mm"
include "wfal.mm"
include "wi.mm"
include "tbw-negdf.mm"
include "tbwlem5.mm"
include "ax-mp.mm"
include "tbw-ax4.mm"
include "tbw-ax1.mm"
include "tbwlem1.mm"
include "mpsyl.mm"

theorem re1luk3
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( -. ph -> ps ) )

  proof
    wph
    wn
    #
    wph
    wfal
    wi
    #
    wi
    #
    wph
    @1
    wps
    wi
    #
    @0
    wps
    wi
    @2
    @1
    @0
    wi
    #
    wfal
    wi
    wi
    wfal
    wi
    @2
    wph
    tbw-negdf
    @2
    @4
    tbwlem5
    ax-mp
    @1
    wph
    wps
    wi
    #
    wi
    #
    wph
    @3
    wi
    wfal
    wps
    wi
    #
    @6
    wps
    tbw-ax4
    @1
    @7
    @5
    wi
    wi
    @7
    @6
    wi
    wph
    wfal
    wps
    tbw-ax1
    @1
    @7
    @5
    tbwlem1
    ax-mp
    ax-mp
    @1
    wph
    wps
    tbwlem1
    ax-mp
    @0
    @1
    wps
    tbw-ax1
    mpsyl
end
