include "wn.mm"
include "wi.mm"
include "wfal.mm"
include "tbw-negdf.mm"
include "tbw-ax2.mm"
include "tbwlem4.mm"
include "ax-mp.mm"
include "tbw-ax1.mm"
include "tbw-ax3.mm"
include "tbwsyl.mm"

theorem re1luk2
  let wph: wff ph


  assert |- ( ( -. ph -> ph ) -> ph )

  proof
    wph
    wn
    #
    wph
    wi
    #
    wph
    wfal
    wi
    #
    wph
    wi
    #
    wph
    @2
    @0
    wi
    #
    @1
    @3
    wi
    @0
    @2
    wi
    #
    @4
    wfal
    wi
    #
    wi
    #
    wfal
    wi
    #
    @4
    wph
    tbw-negdf
    @6
    @7
    wi
    @8
    @4
    wi
    @6
    @5
    tbw-ax2
    @4
    @7
    tbwlem4
    ax-mp
    ax-mp
    @2
    @0
    wph
    tbw-ax1
    ax-mp
    wph
    wfal
    tbw-ax3
    tbwsyl
end
