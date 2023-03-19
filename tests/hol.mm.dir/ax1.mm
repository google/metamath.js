include "kt.mm"
include "tim.mm"
include "kbr.mm"
include "kct.mm"
include "wtru.mm"
include "simpr.mm"
include "adantr.mm"
include "ex.mm"

theorem ax1
  let tr: term R
  let ts: term S
  assume ax1.1: |- R : bool
  assume ax1.2: |- S : bool


  assert |- T. |= [ R ==> [ S ==> R ] ]

  proof
    kt
    tr
    ts
    tr
    tim
    kbr
    kt
    tr
    kct
    #
    ts
    tr
    @0
    ts
    tr
    kt
    tr
    wtru
    ax1.1
    simpr
    ax1.2
    adantr
    ex
    ex
end
