include "wfal.mm"
include "wi.mm"
include "tbw-ax3.mm"
include "tbw-ax2.mm"
include "tbw-ax1.mm"
include "tbwsyl.mm"
include "ax-mp.mm"

theorem tbwlem3
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ( ( ph -> F. ) -> ph ) -> ph ) -> ps ) -> ps )

  proof
    wph
    wfal
    wi
    wph
    wi
    wph
    wi
    #
    wps
    wi
    #
    @1
    wps
    wi
    #
    wi
    #
    @2
    @0
    @3
    wph
    wfal
    tbw-ax3
    @0
    @1
    @0
    wi
    @3
    @0
    @1
    tbw-ax2
    @1
    @0
    wps
    tbw-ax1
    tbwsyl
    ax-mp
    @3
    @2
    wps
    wi
    @2
    wi
    @2
    @1
    @2
    wps
    tbw-ax1
    @2
    wps
    tbw-ax3
    tbwsyl
    ax-mp
end
