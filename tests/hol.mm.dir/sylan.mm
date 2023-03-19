include "kct.mm"
include "ax-cb1.mm"
include "wctr.mm"
include "adantr.mm"
include "simpr.mm"
include "syl2anc.mm"

theorem sylan
  param ta: term A
  param tr: term R
  param ts: term S
  param tt: term T
  assume sylan.1: |- R |= S
  assume sylan.2: |- ( S , T ) |= A


  assert |- ( R , T ) |= A

  proof
    ta
    tr
    tt
    kct
    ts
    tt
    tr
    tt
    ts
    sylan.1
    ts
    tt
    ta
    ts
    tt
    kct
    sylan.2
    ax-cb1
    wctr
    #
    adantr
    tr
    tt
    ts
    tr
    sylan.1
    ax-cb1
    @0
    simpr
    sylan.2
    syl2anc
end
