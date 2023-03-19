include "wn.mm"
include "notnotr.mm"
include "ax-mp.mm"

theorem notnotriOLD
  let wph: wff ph
  assume notnotri.1: |- -. -. ph


  assert |- ph

  proof
    wph
    wn
    wn
    wph
    notnotri.1
    wph
    notnotr
    ax-mp
end
