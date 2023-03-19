include "wfal.mm"
include "wi.mm"
include "merco1lem8.mm"
include "ax-mp.mm"

theorem merco1lem9
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) )

  proof
    wfal
    wph
    wi
    #
    wph
    wph
    wps
    wi
    #
    wi
    @1
    wi
    #
    wi
    #
    @2
    @0
    wph
    wps
    merco1lem8
    @3
    wph
    wps
    merco1lem8
    ax-mp
end
