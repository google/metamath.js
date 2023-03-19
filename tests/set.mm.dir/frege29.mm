include "wi.mm"
include "wn.mm"
include "ax-frege28.mm"
include "frege5.mm"
include "ax-mp.mm"

theorem frege29
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( -. ch -> -. ps ) ) )

  proof
    wps
    wch
    wi
    #
    wch
    wn
    wps
    wn
    wi
    #
    wi
    wph
    @0
    wi
    wph
    @1
    wi
    wi
    wps
    wch
    ax-frege28
    @0
    @1
    wph
    frege5
    ax-mp
end
