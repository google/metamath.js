include "wi.mm"
include "wfal.mm"
include "merco1lem13.mm"
include "merco1lem8.mm"
include "merco1.mm"
include "ax-mp.mm"
include "merco1lem9.mm"
include "merco1lem12.mm"

theorem merco1lem14
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ( ph -> ps ) -> ps ) -> ch ) -> ( ph -> ch ) )

  proof
    wch
    wph
    wi
    #
    wph
    wfal
    wi
    wi
    wph
    wi
    wph
    wps
    wi
    #
    wps
    wi
    #
    wi
    #
    @2
    wch
    wi
    wph
    wch
    wi
    wi
    wph
    @2
    wi
    #
    @3
    @1
    @2
    wi
    @2
    wi
    #
    @4
    wi
    #
    @4
    wph
    wps
    @1
    @2
    merco1lem13
    @6
    @6
    @4
    wi
    #
    wi
    #
    @7
    @4
    wph
    wi
    @6
    wfal
    wi
    wi
    wph
    wi
    #
    @5
    wi
    @8
    @9
    @1
    wps
    merco1lem8
    @4
    wph
    @6
    wph
    @5
    merco1
    ax-mp
    @6
    @4
    merco1lem9
    ax-mp
    ax-mp
    wph
    @2
    @0
    wfal
    merco1lem12
    ax-mp
    wch
    wph
    wph
    wph
    @2
    merco1
    ax-mp
end
