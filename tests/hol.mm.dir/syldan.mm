include "kct.mm"
include "ax-cb1.mm"
include "wctl.mm"
include "wctr.mm"
include "simpl.mm"
include "syl2anc.mm"

theorem syldan
  param ta: term A
  param tr: term R
  param ts: term S
  param tt: term T
  assume syldan.1: |- ( R , S ) |= T
  assume syldan.2: |- ( R , T ) |= A


  assert |- ( R , S ) |= A

  proof
    ta
    tr
    ts
    kct
    #
    tr
    tt
    tr
    ts
    tr
    ts
    tt
    @0
    syldan.1
    ax-cb1
    #
    wctl
    tr
    ts
    @1
    wctr
    simpl
    syldan.1
    syldan.2
    syl2anc
end
