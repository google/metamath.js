include "wi.mm"
include "wfal.mm"
include "merco1lem3.mm"
include "merco1.mm"
include "ax-mp.mm"

theorem merco1lem4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) )

  proof
    wch
    wph
    wi
    #
    wps
    wfal
    wi
    #
    wi
    #
    wps
    wi
    wph
    wps
    wi
    #
    wi
    #
    @3
    wch
    wi
    wps
    wch
    wi
    wi
    @1
    wph
    wfal
    wi
    #
    wi
    @0
    wfal
    wi
    #
    wi
    @2
    wi
    @4
    @1
    @5
    @0
    merco1lem3
    wps
    wfal
    wph
    @6
    @2
    merco1
    ax-mp
    wch
    wph
    wps
    wps
    @3
    merco1
    ax-mp
end
