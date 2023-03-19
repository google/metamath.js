include "wi.mm"
include "wn.mm"
include "frege27.mm"
include "ax-frege41.mm"
include "ax-mp.mm"

theorem frege42
  let wph: wff ph


  assert |- -. -. ( ph -> ph )

  proof
    wph
    wph
    wi
    #
    @0
    wn
    wn
    wph
    frege27
    @0
    ax-frege41
    ax-mp
end
