include "wn.mm"
include "wi.mm"
include "meredith.mm"
include "ax-mp.mm"

theorem merlem1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta


  assert |- ( ( ( ch -> ( -. ph -> ps ) ) -> ta ) -> ( ph -> ta ) )

  proof
    wta
    wph
    wn
    #
    wi
    @0
    wps
    wi
    #
    wn
    #
    @0
    wi
    wi
    #
    @1
    wi
    wch
    @1
    wi
    #
    wi
    #
    @4
    wta
    wi
    wph
    wta
    wi
    wi
    @1
    wta
    wn
    wch
    wn
    wi
    #
    wn
    @2
    wn
    wi
    #
    wi
    @6
    wi
    wta
    wi
    @3
    wi
    @5
    @0
    wps
    @6
    @2
    wta
    meredith
    @1
    @7
    wta
    wch
    @3
    meredith
    ax-mp
    wta
    @0
    @1
    wph
    @4
    meredith
    ax-mp
end
