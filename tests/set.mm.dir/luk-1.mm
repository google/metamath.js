include "wi.mm"
include "wn.mm"
include "meredith.mm"
include "merlem13.mm"
include "ax-mp.mm"

theorem luk-1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) )

  proof
    wch
    wch
    wi
    #
    wph
    wn
    #
    wn
    #
    wn
    @1
    wi
    wi
    @2
    wi
    wps
    wi
    #
    wps
    wch
    wi
    wph
    wch
    wi
    wi
    #
    wi
    #
    wph
    wps
    wi
    #
    @4
    wi
    #
    wch
    wch
    @2
    wph
    wps
    meredith
    @4
    wph
    wi
    #
    @6
    wn
    #
    wn
    #
    wn
    @9
    wi
    wi
    @10
    wi
    @3
    wi
    #
    @5
    @7
    wi
    @6
    @3
    wi
    @11
    wph
    wps
    @1
    @0
    merlem13
    @6
    @3
    @9
    @8
    merlem13
    ax-mp
    @4
    wph
    @10
    @6
    @3
    meredith
    ax-mp
    ax-mp
end
