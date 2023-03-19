include "wi.mm"
include "merco1lem14.mm"
include "merco1lem13.mm"
include "ax-mp.mm"

theorem merco1lem15
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) )

  proof
    wph
    wps
    wi
    #
    wps
    wi
    wch
    wps
    wi
    #
    wi
    wph
    @1
    wi
    #
    wi
    @0
    @2
    wi
    wph
    wps
    @1
    merco1lem14
    @0
    wps
    wch
    @2
    merco1lem13
    ax-mp
end
