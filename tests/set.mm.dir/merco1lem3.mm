include "wi.mm"
include "wfal.mm"
include "merco1lem2.mm"
include "retbwax2.mm"
include "ax-mp.mm"

theorem merco1lem3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) -> ( ch -> F. ) ) -> ( ch -> ph ) )

  proof
    wph
    wph
    wph
    wi
    #
    wph
    wfal
    wi
    wi
    #
    @0
    wi
    #
    wi
    #
    wph
    wps
    wi
    wch
    wfal
    wi
    wi
    #
    wch
    wph
    wi
    #
    wi
    #
    @0
    wfal
    wi
    @1
    wfal
    wi
    wi
    #
    @3
    wph
    wph
    wfal
    wph
    merco1lem2
    @2
    @3
    wi
    @7
    @3
    wi
    @2
    wph
    retbwax2
    @1
    @0
    @3
    wfal
    merco1lem2
    ax-mp
    ax-mp
    @5
    wfal
    wi
    @4
    wfal
    wi
    wi
    #
    @3
    @6
    wi
    #
    wch
    wph
    wfal
    wps
    merco1lem2
    @6
    @9
    wi
    @8
    @9
    wi
    @6
    @3
    retbwax2
    @4
    @5
    @9
    wfal
    merco1lem2
    ax-mp
    ax-mp
    ax-mp
end
