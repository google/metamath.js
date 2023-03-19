include "wi.mm"
include "wn.mm"
include "frege42.mm"
include "frege40.mm"
include "ax-mp.mm"

theorem frege43
  let wph: wff ph


  assert |- ( ( -. ph -> ph ) -> ph )

  proof
    wph
    wph
    wi
    wn
    #
    wn
    wph
    wn
    wph
    wi
    wph
    wi
    wph
    frege42
    @0
    wph
    frege40
    ax-mp
end
