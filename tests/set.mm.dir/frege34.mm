include "wn.mm"
include "wi.mm"
include "frege33.mm"
include "frege5.mm"
include "ax-mp.mm"

theorem frege34
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( -. ps -> ch ) ) -> ( ph -> ( -. ch -> ps ) ) )

  proof
    wps
    wn
    wch
    wi
    #
    wch
    wn
    wps
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
    frege33
    @0
    @1
    wph
    frege5
    ax-mp
end
