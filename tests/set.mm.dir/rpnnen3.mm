include "cq.mm"
include "cpw.mm"
include "cvv.mm"
include "wcel.mm"
include "cr.mm"
include "cdom.mm"
include "wbr.mm"
include "qex.mm"
include "pwex.mm"
include "cv.mm"
include "clt.mm"
include "crab.mm"
include "wss.mm"
include "ssrab2.mm"
include "elpw2.mm"
include "mpbir.mm"
include "a1i.mm"
include "wa.mm"
include "wceq.mm"
include "wne.mm"
include "wo.mm"
include "lttri2.mm"
include "rpnnen3lem.mm"
include "ancom1s.mm"
include "necomd.mm"
include "jaodan.mm"
include "ex.mm"
include "sylbid.mm"
include "necon4d.mm"
include "breq2.mm"
include "rabbidv.mm"
include "impbid1.mm"
include "dom2.mm"
include "ax-mp.mm"

theorem rpnnen3
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d


  assert |- RR ~<_ ~P QQ

  proof
    cq
    cpw
    #
    cvv
    wcel
    cr
    @0
    cdom
    wbr
    cq
    qex
    pwex
    va
    vb
    cr
    @0
    vc
    cv
    #
    va
    cv
    #
    clt
    wbr
    #
    vc
    cq
    crab
    #
    @1
    vb
    cv
    #
    clt
    wbr
    #
    vc
    cq
    crab
    #
    cvv
    @4
    @0
    wcel
    #
    @2
    cr
    wcel
    #
    @8
    @4
    cq
    wss
    @3
    vc
    cq
    ssrab2
    @4
    cq
    qex
    elpw2
    mpbir
    a1i
    @9
    @5
    cr
    wcel
    #
    wa
    #
    @4
    @7
    wceq
    @2
    @5
    wceq
    #
    @11
    @2
    @5
    @4
    @7
    @11
    @2
    @5
    wne
    @2
    @5
    clt
    wbr
    #
    @5
    @2
    clt
    wbr
    #
    wo
    #
    @4
    @7
    wne
    #
    @2
    @5
    lttri2
    @11
    @15
    @16
    @11
    @13
    @16
    @14
    va
    vb
    vc
    rpnnen3lem
    @11
    @14
    wa
    @7
    @4
    @10
    @9
    @14
    @7
    @4
    wne
    vb
    va
    vc
    rpnnen3lem
    ancom1s
    necomd
    jaodan
    ex
    sylbid
    necon4d
    @12
    @3
    @6
    vc
    cq
    @2
    @5
    @1
    clt
    breq2
    rabbidv
    impbid1
    dom2
    ax-mp
end
