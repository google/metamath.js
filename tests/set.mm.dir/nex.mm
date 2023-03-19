include "wn.mm"
include "wex.mm"
include "alnex.mm"
include "mpgbi.mm"

theorem nex
  let wph: wff ph
  let vx: setvar x
  assume nex.1: |- -. ph


  assert |- -. E. x ph

  proof
    wph
    wn
    wph
    vx
    wex
    wn
    vx
    wph
    vx
    alnex
    nex.1
    mpgbi
end
