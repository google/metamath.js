include "wi.mm"
include "wfal.mm"
include "merco1lem5.mm"
include "merco1lem3.mm"
include "ax-mp.mm"
include "merco1.mm"

theorem merco1lem6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ph -> ps ) ) -> ( ch -> ( ph -> ps ) ) )

  proof
    wph
    wps
    wi
    #
    wfal
    wi
    wch
    wfal
    wi
    #
    wi
    #
    wfal
    wi
    #
    wph
    wi
    #
    wph
    @0
    wi
    wch
    @0
    wi
    wi
    @0
    @3
    wfal
    wi
    #
    wi
    #
    @4
    @2
    @5
    wi
    #
    @6
    @5
    wfal
    wi
    @3
    wi
    @7
    @2
    wfal
    wfal
    merco1lem5
    @5
    wfal
    @2
    merco1lem3
    ax-mp
    @0
    @1
    @5
    merco1lem5
    ax-mp
    wph
    wps
    @3
    merco1lem3
    ax-mp
    @0
    wfal
    wch
    wfal
    wph
    merco1
    ax-mp
end
