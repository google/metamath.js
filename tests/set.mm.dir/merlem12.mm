include "wn.mm"
include "wi.mm"
include "merlem5.mm"
include "merlem2.mm"
include "ax-mp.mm"
include "merlem4.mm"
include "merlem11.mm"

theorem merlem12
  let wph: wff ph
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( th -> ( -. -. ch -> ch ) ) -> ph ) -> ph )

  proof
    wth
    wch
    wn
    wn
    wch
    wi
    #
    wi
    #
    wph
    wi
    #
    @2
    wph
    wi
    #
    wi
    #
    @3
    @1
    @4
    wch
    wch
    wi
    @0
    wi
    @1
    wch
    wch
    merlem5
    wch
    @0
    wth
    merlem2
    ax-mp
    wph
    @2
    @1
    merlem4
    ax-mp
    @2
    wph
    merlem11
    ax-mp
end
