include "con0.mm"
include "cvv.mm"
include "cr1.mm"
include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wfn.mm"
include "r1fnon.mm"
include "dffn2.mm"
include "mpbi.mm"
include "wcel.mm"
include "wa.mm"
include "wel.mm"
include "w3o.mm"
include "word.mm"
include "eloni.mm"
include "ordtri3or.mm"
include "syl2an.mm"
include "w3a.mm"
include "wn.mm"
include "csdm.mm"
include "wbr.mm"
include "sdomirr.mm"
include "r1sdom.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "mtoi.mm"
include "3adant1.mm"
include "pm2.21d.mm"
include "3expia.mm"
include "ax-1.mm"
include "a1i.mm"
include "breq2.mm"
include "3adant2.mm"
include "3jaod.mm"
include "mpd.mm"
include "rgen2a.mm"
include "dff13.mm"
include "mpbir2an.mm"

theorem r111
  let vx: setvar x
  let vy: setvar y


  assert |- R1 : On -1-1-> _V

  proof
    con0
    cvv
    cr1
    wf1
    con0
    cvv
    cr1
    wf
    #
    vx
    cv
    #
    cr1
    cfv
    #
    vy
    cv
    #
    cr1
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    con0
    wral
    vx
    con0
    wral
    cr1
    con0
    wfn
    @0
    r1fnon
    con0
    cr1
    dffn2
    mpbi
    @7
    vx
    vy
    con0
    @1
    con0
    wcel
    #
    @3
    con0
    wcel
    #
    wa
    #
    vx
    vy
    wel
    #
    @6
    vy
    vx
    wel
    #
    w3o
    #
    @7
    @8
    @1
    word
    @3
    word
    @13
    @9
    @1
    eloni
    @3
    eloni
    @1
    @3
    ordtri3or
    syl2an
    @10
    @11
    @7
    @6
    @12
    @8
    @9
    @11
    @7
    @8
    @9
    @11
    w3a
    @5
    @6
    @9
    @11
    @5
    wn
    #
    @8
    @9
    @11
    wa
    #
    @5
    @4
    @4
    csdm
    wbr
    #
    @4
    sdomirr
    #
    @15
    @2
    @4
    csdm
    wbr
    @5
    @16
    @3
    @1
    r1sdom
    @2
    @4
    @4
    csdm
    breq1
    syl5ibcom
    mtoi
    3adant1
    pm2.21d
    3expia
    @6
    @7
    wi
    @10
    @6
    @5
    ax-1
    a1i
    @8
    @9
    @12
    @7
    @8
    @9
    @12
    w3a
    @5
    @6
    @8
    @12
    @14
    @9
    @8
    @12
    wa
    #
    @5
    @16
    @17
    @18
    @4
    @2
    csdm
    wbr
    @5
    @16
    @1
    @3
    r1sdom
    @2
    @4
    @4
    csdm
    breq2
    syl5ibcom
    mtoi
    3adant2
    pm2.21d
    3expia
    3jaod
    mpd
    rgen2a
    vx
    vy
    con0
    cvv
    cr1
    dff13
    mpbir2an
end
