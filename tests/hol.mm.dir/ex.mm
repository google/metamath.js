include "tan.mm"
include "kbr.mm"
include "ke.mm"
include "tim.mm"
include "hb.mm"
include "kct.mm"
include "wan.mm"
include "ax-cb1.mm"
include "wctr.mm"
include "ax-cb2.mm"
include "wov.mm"
include "wctl.mm"
include "dfan2.mm"
include "a1i.mm"
include "wct.mm"
include "simpr.mm"
include "simpld.mm"
include "jca.mm"
include "ded.mm"
include "eqtri.mm"
include "imval.mm"
include "mpbir.mm"

theorem ex
  let tr: term R
  let ts: term S
  let tt: term T
  assume ex.1: |- ( R , S ) |= T


  assert |- R |= [ S ==> T ]

  proof
    ts
    tt
    tan
    kbr
    #
    ts
    ke
    kbr
    #
    ts
    tt
    tim
    kbr
    #
    tr
    hb
    @0
    ts
    tt
    kct
    #
    ts
    tr
    hb
    hb
    hb
    ts
    tt
    tan
    wan
    tr
    ts
    tt
    tr
    ts
    kct
    #
    ex.1
    ax-cb1
    #
    wctr
    #
    tt
    @4
    ex.1
    ax-cb2
    #
    wov
    @0
    @3
    ke
    kbr
    tr
    tr
    ts
    @5
    wctl
    #
    ts
    tt
    @6
    @7
    dfan2
    a1i
    tr
    @3
    ts
    tr
    @3
    kct
    ts
    tt
    tr
    @3
    @8
    ts
    tt
    @6
    @7
    wct
    simpr
    simpld
    @4
    ts
    tt
    tr
    ts
    @8
    @6
    simpr
    ex.1
    jca
    ded
    eqtri
    #
    @2
    @1
    ke
    kbr
    tr
    @1
    tr
    @9
    ax-cb1
    ts
    tt
    @6
    @7
    imval
    a1i
    mpbir
end
