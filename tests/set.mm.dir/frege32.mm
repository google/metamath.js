include "wn.mm"
include "wi.mm"
include "ax-frege31.mm"
include "frege7.mm"
include "ax-mp.mm"

theorem frege32
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( -. ph -> ps ) -> ( -. ps -> -. -. ph ) ) -> ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) )

  proof
    wph
    wn
    #
    wn
    #
    wph
    wi
    @0
    wps
    wi
    #
    wps
    wn
    #
    @1
    wi
    wi
    @2
    @3
    wph
    wi
    wi
    wi
    wph
    ax-frege31
    @1
    wph
    @2
    @3
    frege7
    ax-mp
end
