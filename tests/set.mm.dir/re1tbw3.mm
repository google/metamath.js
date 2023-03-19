include "wi.mm"
include "mercolem2.mm"
include "mercolem6.mm"
include "ax-mp.mm"

theorem re1tbw3
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph -> ps ) -> ph ) -> ph )

  proof
    wph
    wph
    wi
    #
    wph
    wi
    wph
    @0
    wi
    wi
    #
    wph
    wps
    wi
    wph
    wi
    #
    wph
    wi
    #
    wph
    wph
    wph
    wph
    mercolem2
    @2
    @1
    @3
    wi
    #
    wi
    @4
    wph
    wps
    @1
    @2
    mercolem2
    @2
    @1
    wph
    mercolem6
    ax-mp
    ax-mp
end
