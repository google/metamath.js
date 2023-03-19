include "wi.mm"
include "wn.mm"
include "merlem2.mm"
include "ax-mp.mm"
include "meredith.mm"

theorem merlem3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ps -> ch ) -> ph ) -> ( ch -> ph ) )

  proof
    wph
    wph
    wi
    #
    wch
    wn
    #
    @1
    wi
    #
    wi
    #
    wch
    wi
    wps
    wch
    wi
    #
    wi
    #
    @4
    wph
    wi
    wch
    wph
    wi
    #
    wi
    @6
    wps
    wn
    #
    @7
    wi
    wi
    wps
    wi
    #
    @3
    wi
    #
    @5
    @2
    @2
    wi
    @3
    wi
    @9
    @1
    @2
    @0
    merlem2
    @2
    @3
    @8
    merlem2
    ax-mp
    wch
    wph
    wps
    wps
    @3
    meredith
    ax-mp
    wph
    wph
    wch
    wch
    @4
    meredith
    ax-mp
end
