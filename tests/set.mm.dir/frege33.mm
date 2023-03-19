include "wn.mm"
include "wi.mm"
include "ax-frege28.mm"
include "frege32.mm"
include "ax-mp.mm"

theorem frege33
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) )

  proof
    wph
    wn
    #
    wps
    wi
    #
    wps
    wn
    #
    @0
    wn
    wi
    wi
    @1
    @2
    wph
    wi
    wi
    @0
    wps
    ax-frege28
    wph
    wps
    frege32
    ax-mp
end
