include "wn.mm"
include "wi.mm"
include "frege47.mm"
include "frege12.mm"
include "ax-mp.mm"

theorem frege49
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( -. ph -> ps ) -> ( ( ph -> ch ) -> ( ( ps -> ch ) -> ch ) ) )

  proof
    wph
    wn
    wps
    wi
    #
    wps
    wch
    wi
    #
    wph
    wch
    wi
    #
    wch
    wi
    wi
    wi
    @0
    @2
    @1
    wch
    wi
    wi
    wi
    wph
    wps
    wch
    frege47
    @0
    @1
    @2
    wch
    frege12
    ax-mp
end
