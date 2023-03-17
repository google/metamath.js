include "kct.mm"
include "ax-cb1.mm"
include "wctr.mm"
include "wctl.mm"
include "simpr.mm"
include "simpl.mm"
include "syl2anc.mm"

theorem ancoms
  let tr: term R
  let ts: term S
  let tt: term T
  assume ancoms.1: |- ( R , S ) |= T


  assert |- ( S , R ) |= T

  proof
    tt
    ts
    tr
    kct
    tr
    ts
    ts
    tr
    tr
    ts
    tt
    tr
    ts
    kct
    ancoms.1
    ax-cb1
    #
    wctr
    #
    tr
    ts
    @0
    wctl
    #
    simpr
    ts
    tr
    @1
    @2
    simpl
    ancoms.1
    syl2anc
end
