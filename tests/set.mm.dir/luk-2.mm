include "wn.mm"
include "wi.mm"
include "merlem5.mm"
include "merlem4.mm"
include "ax-mp.mm"
include "merlem11.mm"
include "meredith.mm"

theorem luk-2
  let wph: wff ph


  assert |- ( ( -. ph -> ph ) -> ph )

  proof
    wph
    wn
    #
    wph
    wi
    #
    @1
    wph
    wi
    #
    wi
    #
    @2
    wph
    @1
    wn
    #
    wi
    @0
    wn
    @4
    wi
    wi
    #
    @0
    wi
    #
    @0
    wi
    #
    @3
    @6
    @7
    wi
    #
    @7
    @5
    @8
    wph
    @4
    merlem5
    @0
    @6
    @5
    merlem4
    ax-mp
    @6
    @0
    merlem11
    ax-mp
    wph
    @4
    @0
    @1
    @0
    meredith
    ax-mp
    @1
    wph
    merlem11
    ax-mp
end
