include "kct.mm"
include "ax-cb2.mm"
include "wctl.mm"
include "wctr.mm"
include "simpr.mm"
include "syl.mm"

theorem simprd
  let tr: term R
  let ts: term S
  let tt: term T
  assume simpld.1: |- R |= ( S , T )


  assert |- R |= T

  proof
    tr
    ts
    tt
    kct
    #
    tt
    simpld.1
    ts
    tt
    ts
    tt
    @0
    tr
    simpld.1
    ax-cb2
    #
    wctl
    ts
    tt
    @1
    wctr
    simpr
    syl
end
