include "wi.mm"
include "wfal.mm"
include "merco1lem5.mm"
include "merco1lem3.mm"
include "ax-mp.mm"
include "merco1lem4.mm"
include "merco1.mm"
include "merco1lem2.mm"

theorem merco1lem11
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta


  assert |- ( ( ph -> ps ) -> ( ( ( ch -> ( ph -> ta ) ) -> F. ) -> ps ) )

  proof
    wph
    wta
    wi
    #
    wps
    wph
    wi
    #
    wch
    @0
    wi
    #
    wfal
    wi
    #
    wfal
    wi
    #
    wi
    #
    wfal
    wi
    #
    wfal
    wi
    #
    wi
    #
    wph
    wps
    wi
    @3
    wps
    wi
    wi
    #
    @2
    @7
    wi
    #
    @8
    @4
    @7
    wi
    #
    @10
    @5
    @7
    wi
    #
    @11
    @7
    wfal
    wi
    @6
    wi
    @12
    @5
    wfal
    wfal
    merco1lem5
    @7
    wfal
    @5
    merco1lem3
    ax-mp
    @1
    @4
    @7
    merco1lem4
    ax-mp
    @2
    wfal
    @7
    merco1lem5
    ax-mp
    wch
    @0
    @7
    merco1lem4
    ax-mp
    @6
    wph
    wi
    @9
    wi
    @8
    @9
    wi
    wps
    wph
    @3
    wfal
    wph
    merco1
    @6
    wph
    @9
    wta
    merco1lem2
    ax-mp
    ax-mp
end
