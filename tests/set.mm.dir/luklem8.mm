include "wi.mm"
include "luk-1.mm"
include "luklem7.mm"
include "ax-mp.mm"

theorem luklem8
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) )

  proof
    wch
    wph
    wi
    #
    wph
    wps
    wi
    #
    wch
    wps
    wi
    #
    wi
    wi
    @1
    @0
    @2
    wi
    wi
    wch
    wph
    wps
    luk-1
    @0
    @1
    @2
    luklem7
    ax-mp
end
