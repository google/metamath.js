include "wn.mm"
include "notnot.mm"
include "ax-mp.mm"

theorem notnoti
  let wph: wff ph
  assume notnoti.1: |- ph


  assert |- -. -. ph

  proof
    wph
    wph
    wn
    wn
    notnoti.1
    wph
    notnot
    ax-mp
end
