include "wi.mm"
include "wn.mm"
include "merlem1.mm"
include "meredith.mm"
include "ax-mp.mm"

theorem merlem2
  let wph: wff ph
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph -> ph ) -> ch ) -> ( th -> ch ) )

  proof
    wch
    wch
    wi
    #
    wph
    wn
    wth
    wn
    #
    wi
    wi
    wph
    wi
    wph
    wph
    wi
    #
    wi
    @2
    wch
    wi
    wth
    wch
    wi
    wi
    wph
    @1
    @0
    wph
    merlem1
    wch
    wch
    wph
    wth
    @2
    meredith
    ax-mp
end
