include "kct.mm"
include "ax-cb1.mm"
include "wctl.mm"
include "wctr.mm"
include "simpl.mm"
include "adantr.mm"
include "simpr.mm"
include "ct1.mm"
include "syl2anc.mm"

theorem anassrs
  let ta: term A
  let tr: term R
  let ts: term S
  let tt: term T
  assume anassrs.1: |- ( R , ( S , T ) ) |= A


  assert |- ( ( R , S ) , T ) |= A

  proof
    ta
    tr
    ts
    kct
    #
    tt
    kct
    tr
    ts
    tt
    kct
    #
    @0
    tt
    tr
    tr
    ts
    tr
    @1
    ta
    tr
    @1
    kct
    anassrs.1
    ax-cb1
    #
    wctl
    #
    ts
    tt
    tr
    @1
    @2
    wctr
    #
    wctl
    #
    simpl
    ts
    tt
    @4
    wctr
    #
    adantr
    @0
    ts
    tt
    tr
    ts
    @3
    @5
    simpr
    @6
    ct1
    anassrs.1
    syl2anc
end
