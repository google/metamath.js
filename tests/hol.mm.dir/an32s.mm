include "kct.mm"
include "ax-cb1.mm"
include "wctl.mm"
include "wctr.mm"
include "simpl.mm"
include "ct1.mm"
include "simpr.mm"
include "adantr.mm"
include "syl2anc.mm"

theorem an32s
  let ta: term A
  let tr: term R
  let ts: term S
  let tt: term T
  assume an32s.1: |- ( ( R , S ) , T ) |= A


  assert |- ( ( R , T ) , S ) |= A

  proof
    ta
    tr
    tt
    kct
    #
    ts
    kct
    tr
    ts
    kct
    #
    tt
    @0
    tr
    ts
    tr
    tt
    tr
    ts
    @1
    tt
    ta
    @1
    tt
    kct
    an32s.1
    ax-cb1
    #
    wctl
    #
    wctl
    #
    @1
    tt
    @2
    wctr
    #
    simpl
    tr
    ts
    @3
    wctr
    #
    ct1
    @0
    ts
    tt
    tr
    tt
    @4
    @5
    simpr
    @6
    adantr
    an32s.1
    syl2anc
end
