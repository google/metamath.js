include "wi.mm"
include "merco1lem6.mm"
include "ax-mp.mm"

theorem merco1lem8
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ph -> ( ( ps -> ( ps -> ch ) ) -> ( ps -> ch ) ) )

  proof
    wps
    wps
    wch
    wi
    #
    wi
    #
    @1
    @0
    wi
    #
    wi
    wph
    @2
    wi
    wps
    wch
    @1
    merco1lem6
    @1
    @0
    wph
    merco1lem6
    ax-mp
end
