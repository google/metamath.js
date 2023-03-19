include "wi.mm"
include "wfal.mm"
include "merco2.mm"
include "mercolem3.mm"
include "mercolem6.mm"
include "ax-mp.mm"
include "mercolem5.mm"
include "mercolem4.mm"

theorem mercolem7
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ps ) -> ( ( ( ph -> ch ) -> ( th -> ps ) ) -> ( th -> ps ) ) )

  proof
    wph
    wph
    wi
    #
    wfal
    wph
    wi
    wph
    wi
    wi
    @0
    wph
    @0
    wi
    wi
    wi
    #
    wph
    wps
    wi
    #
    wph
    wch
    wi
    #
    wth
    wps
    wi
    #
    wi
    #
    @4
    wi
    #
    wi
    #
    wph
    wph
    wph
    wph
    wph
    wph
    merco2
    @3
    @6
    wi
    #
    @1
    @7
    wi
    #
    @5
    @8
    wi
    @8
    @5
    @3
    @4
    mercolem3
    @5
    @3
    @4
    mercolem6
    ax-mp
    wph
    @7
    wi
    @8
    @9
    wi
    wps
    wth
    wph
    @5
    mercolem5
    @6
    wch
    wph
    @1
    @2
    mercolem4
    ax-mp
    ax-mp
    ax-mp
end
