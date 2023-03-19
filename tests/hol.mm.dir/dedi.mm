include "kt.mm"
include "wtru.mm"
include "adantl.mm"
include "ded.mm"

theorem dedi
  let ts: term S
  let tt: term T
  assume dedi.1: |- S |= T
  assume dedi.2: |- T |= S


  assert |- T. |= [ S = T ]

  proof
    kt
    ts
    tt
    ts
    kt
    tt
    dedi.1
    wtru
    adantl
    tt
    kt
    ts
    dedi.2
    wtru
    adantl
    ded
end
