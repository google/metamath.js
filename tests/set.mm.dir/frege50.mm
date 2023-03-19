include "wn.mm"
include "wi.mm"
include "frege49.mm"
include "frege17.mm"
include "ax-mp.mm"

theorem frege50
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ch -> ps ) -> ( ( -. ph -> ch ) -> ps ) ) )

  proof
    wph
    wn
    wch
    wi
    #
    wph
    wps
    wi
    #
    wch
    wps
    wi
    #
    wps
    wi
    wi
    wi
    @1
    @2
    @0
    wps
    wi
    wi
    wi
    wph
    wch
    wps
    frege49
    @0
    @1
    @2
    wps
    frege17
    ax-mp
end
