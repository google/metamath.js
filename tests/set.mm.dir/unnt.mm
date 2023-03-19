include "wtru.mm"
include "weu.mm"
include "wn.mm"
include "wex.mm"
include "nextnt.mm"
include "eunex.mm"
include "mto.mm"

theorem unnt
  let vx: setvar x


  assert |- -. E! x T.

  proof
    wtru
    vx
    weu
    wtru
    wn
    vx
    wex
    vx
    nextnt
    wtru
    vx
    eunex
    mto
end
