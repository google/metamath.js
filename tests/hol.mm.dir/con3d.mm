include "tne.mm"
include "kc.mm"
include "hb.mm"
include "wnot.mm"
include "kct.mm"
include "ax-cb2.mm"
include "wc.mm"
include "notnot1.mm"
include "syl.mm"
include "con2d.mm"

theorem con3d
  param tr: term R
  param ts: term S
  param tt: term T
  assume con3d.1: |- ( R , S ) |= T


  assert |- ( R , ( ~ T ) ) |= ( ~ S )

  proof
    tr
    ts
    tne
    tt
    kc
    #
    hb
    hb
    tne
    tt
    wnot
    tt
    tr
    ts
    kct
    #
    con3d.1
    ax-cb2
    #
    wc
    @1
    tt
    tne
    @0
    kc
    con3d.1
    tt
    @2
    notnot1
    syl
    con2d
end
