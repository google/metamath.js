include "wi.mm"
include "wfal.mm"
include "merco1lem4.mm"
include "merco1.mm"
include "ax-mp.mm"

theorem merco1lem5
  let wph: wff ph
  let wch: wff ch
  let wta: wff ta


  assert |- ( ( ( ( ph -> F. ) -> ch ) -> ta ) -> ( ph -> ta ) )

  proof
    wta
    wph
    wi
    #
    wph
    wfal
    wi
    #
    wi
    wch
    wi
    @1
    wch
    wi
    #
    wi
    @2
    wta
    wi
    wph
    wta
    wi
    wi
    @0
    @1
    wch
    merco1lem4
    wta
    wph
    wph
    wch
    @2
    merco1
    ax-mp
end
