include "wn.mm"
include "wi.mm"
include "frege36.mm"
include "frege9.mm"
include "ax-mp.mm"

theorem frege37
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( -. ph -> ps ) -> ch ) -> ( ph -> ch ) )

  proof
    wph
    wph
    wn
    wps
    wi
    #
    wi
    @0
    wch
    wi
    wph
    wch
    wi
    wi
    wph
    wps
    frege36
    wph
    @0
    wch
    frege9
    ax-mp
end
