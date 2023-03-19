include "wfal.mm"
include "wi.mm"
include "tbw-ax4.mm"
include "tbw-ax1.mm"
include "tbwlem1.mm"
include "ax-mp.mm"
include "tbwlem2.mm"
include "tbwlem3.mm"
include "tbwsyl.mm"

theorem tbwlem4
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph -> F. ) -> ps ) -> ( ( ps -> F. ) -> ph ) )

  proof
    wph
    wfal
    wi
    #
    wps
    wi
    #
    @0
    wps
    wfal
    wi
    #
    wfal
    wi
    #
    wi
    #
    @2
    wph
    wi
    #
    wps
    @3
    wi
    #
    @1
    @4
    wi
    #
    @2
    @2
    wi
    #
    @6
    wfal
    wfal
    wi
    #
    @8
    wfal
    tbw-ax4
    @2
    @9
    @2
    wi
    wi
    @9
    @8
    wi
    wps
    wfal
    wfal
    tbw-ax1
    @2
    @9
    @2
    tbwlem1
    ax-mp
    ax-mp
    @2
    wps
    wfal
    tbwlem1
    ax-mp
    @1
    @6
    @4
    wi
    wi
    @6
    @7
    wi
    @0
    wps
    @3
    tbw-ax1
    @1
    @6
    @4
    tbwlem1
    ax-mp
    ax-mp
    @4
    @0
    wph
    wi
    wph
    wi
    @5
    wi
    @5
    @0
    @2
    wph
    wph
    tbwlem2
    wph
    @5
    tbwlem3
    tbwsyl
    tbwsyl
end
