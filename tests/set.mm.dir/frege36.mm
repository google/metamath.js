include "wn.mm"
include "wi.mm"
include "ax-frege1.mm"
include "frege34.mm"
include "ax-mp.mm"

theorem frege36
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( -. ph -> ps ) )

  proof
    wph
    wps
    wn
    #
    wph
    wi
    wi
    wph
    wph
    wn
    wps
    wi
    wi
    wph
    @0
    ax-frege1
    wph
    wps
    wph
    frege34
    ax-mp
end
