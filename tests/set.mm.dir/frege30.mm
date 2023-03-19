include "wi.mm"
include "wn.mm"
include "frege29.mm"
include "frege10.mm"
include "ax-mp.mm"

theorem frege30
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( -. ch -> -. ph ) ) )

  proof
    wps
    wph
    wch
    wi
    wi
    wps
    wch
    wn
    wph
    wn
    wi
    wi
    #
    wi
    wph
    wps
    wch
    wi
    wi
    @0
    wi
    wps
    wph
    wch
    frege29
    wps
    wph
    wch
    @0
    frege10
    ax-mp
end
