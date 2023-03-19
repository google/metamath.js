include "wn.mm"
include "wi.mm"
include "frege46.mm"
include "frege21.mm"
include "ax-mp.mm"

theorem frege47
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( -. ph -> ps ) -> ( ( ps -> ch ) -> ( ( ph -> ch ) -> ch ) ) )

  proof
    wph
    wn
    #
    wch
    wi
    wph
    wch
    wi
    wch
    wi
    #
    wi
    @0
    wps
    wi
    wps
    wch
    wi
    @1
    wi
    wi
    wph
    wch
    frege46
    @0
    wch
    @1
    wps
    frege21
    ax-mp
end
