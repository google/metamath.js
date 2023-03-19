include "wn.mm"
include "wi.mm"
include "frege39.mm"
include "frege35.mm"
include "ax-mp.mm"

theorem frege40
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ph -> ( ( -. ps -> ps ) -> ps ) )

  proof
    wps
    wn
    #
    wps
    wi
    #
    @0
    wph
    wi
    wi
    wph
    wn
    @1
    wps
    wi
    wi
    wps
    wph
    frege39
    @1
    wps
    wph
    frege35
    ax-mp
end
