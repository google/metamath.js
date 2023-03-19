include "wi.mm"
include "wn.mm"
include "merlem6.mm"
include "merlem8.mm"
include "ax-mp.mm"
include "meredith.mm"

theorem merlem9
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ph -> ps ) -> ( ch -> ( th -> ( ps -> ta ) ) ) ) -> ( et -> ( ch -> ( th -> ( ps -> ta ) ) ) ) )

  proof
    wch
    wth
    wps
    wta
    wi
    #
    wi
    #
    wi
    #
    wet
    wn
    #
    wi
    wps
    wn
    #
    @3
    wi
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
    @6
    @2
    wi
    wet
    @2
    wi
    wi
    @0
    @5
    wn
    wth
    wn
    wi
    #
    wn
    wph
    wn
    wi
    #
    wi
    @8
    wi
    @5
    wi
    #
    @7
    @1
    @5
    wi
    @10
    @3
    wch
    @1
    @4
    merlem6
    wth
    @0
    @5
    @9
    merlem8
    ax-mp
    wps
    wta
    @8
    wph
    @5
    meredith
    ax-mp
    @2
    @3
    wps
    wet
    @6
    meredith
    ax-mp
end
