include "kct.mm"
include "tim.mm"
include "kbr.mm"
include "ax-cb1.mm"
include "simpr.mm"
include "adantr.mm"
include "mpd.mm"

theorem imp
  let tr: term R
  let ts: term S
  let tt: term T
  assume imp.1: |- S : bool
  assume imp.2: |- T : bool
  assume imp.3: |- R |= [ S ==> T ]


  assert |- ( R , S ) |= T

  proof
    tr
    ts
    kct
    ts
    tt
    imp.2
    tr
    ts
    ts
    tt
    tim
    kbr
    #
    tr
    imp.3
    ax-cb1
    imp.1
    simpr
    tr
    ts
    @0
    imp.3
    imp.1
    adantr
    mpd
end
