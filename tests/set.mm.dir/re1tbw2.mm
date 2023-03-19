include "wi.mm"
include "mercolem1.mm"
include "ax-mp.mm"
include "mercolem6.mm"

theorem re1tbw2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps -> ph ) )

  proof
    wps
    wph
    wps
    wph
    wi
    #
    wi
    #
    wi
    #
    @1
    wph
    @2
    wi
    #
    @2
    wph
    wph
    wi
    #
    wph
    wi
    @1
    wi
    @3
    wph
    wph
    wph
    wps
    mercolem1
    @4
    wph
    @1
    wps
    mercolem1
    ax-mp
    wph
    wps
    @0
    mercolem6
    ax-mp
    wps
    wph
    wph
    mercolem6
    ax-mp
end
