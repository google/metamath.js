include "wn.mm"
include "wi.mm"
include "frege34.mm"
include "frege12.mm"
include "ax-mp.mm"

theorem frege35
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( -. ps -> ch ) ) -> ( -. ch -> ( ph -> ps ) ) )

  proof
    wph
    wps
    wn
    wch
    wi
    wi
    #
    wph
    wch
    wn
    #
    wps
    wi
    wi
    wi
    @0
    @1
    wph
    wps
    wi
    wi
    wi
    wph
    wps
    wch
    frege34
    @0
    wph
    @1
    wps
    frege12
    ax-mp
end
