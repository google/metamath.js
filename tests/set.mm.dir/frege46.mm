include "wn.mm"
include "wi.mm"
include "frege33.mm"
include "frege45.mm"
include "ax-mp.mm"

theorem frege46
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) )

  proof
    wph
    wn
    wps
    wi
    #
    wps
    wn
    wph
    wi
    wi
    @0
    wph
    wps
    wi
    wps
    wi
    wi
    wph
    wps
    frege33
    wph
    wps
    frege45
    ax-mp
end
