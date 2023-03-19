include "hb.mm"
include "ke.mm"
include "weq.mm"
include "kct.mm"
include "ax-cb2.mm"
include "ax-ded.mm"
include "dfov2.mm"

theorem ded
  param tr: term R
  param ts: term S
  param tt: term T
  assume ded.1: |- ( R , S ) |= T
  assume ded.2: |- ( R , T ) |= S


  assert |- R |= [ S = T ]

  proof
    hb
    hb
    ts
    tt
    ke
    tr
    hb
    weq
    ts
    tr
    tt
    kct
    ded.2
    ax-cb2
    tt
    tr
    ts
    kct
    ded.1
    ax-cb2
    tr
    ts
    tt
    ded.1
    ded.2
    ax-ded
    dfov2
end
