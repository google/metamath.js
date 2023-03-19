include "wfal.mm"
include "wi.mm"
include "tbw-ax2.mm"
include "tbw-ax1.mm"
include "tbwsyl.mm"
include "tbwlem1.mm"
include "ax-mp.mm"
include "tbwlem4.mm"

theorem tbwlem5
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph -> ( ps -> F. ) ) -> F. ) -> ph )

  proof
    wph
    wfal
    wi
    #
    wph
    wps
    wfal
    wi
    #
    wi
    #
    wi
    #
    @2
    wfal
    wi
    wph
    wi
    wph
    @0
    @1
    wi
    #
    wi
    @3
    wph
    wps
    wph
    wi
    @4
    wph
    wps
    tbw-ax2
    wps
    wph
    wfal
    tbw-ax1
    tbwsyl
    wph
    @0
    @1
    tbwlem1
    ax-mp
    wph
    @2
    tbwlem4
    ax-mp
end
