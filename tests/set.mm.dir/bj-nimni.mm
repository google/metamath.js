include "wn.mm"
include "wi.mm"
include "bj-nimn.mm"
include "ax-mp.mm"

theorem bj-nimni
  let wph: wff ph
  assume bj-nimni.1: |- ph


  assert |- -. ( ph -> -. ph )

  proof
    wph
    wph
    wph
    wn
    wi
    wn
    bj-nimni.1
    wph
    bj-nimn
    ax-mp
end
