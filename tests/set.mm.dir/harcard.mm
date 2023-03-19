include "char.mm"
include "cfv.mm"
include "ccrd.mm"
include "wceq.mm"
include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "wss.mm"
include "wi.mm"
include "wral.mm"
include "harcl.mm"
include "wa.mm"
include "cdom.mm"
include "harndom.mm"
include "wn.mm"
include "wb.mm"
include "simpll.mm"
include "simpr.mm"
include "elharval.mm"
include "sylib.mm"
include "simpld.mm"
include "ontri1.mm"
include "syl2anc.mm"
include "simpllr.mm"
include "cvv.mm"
include "vex.mm"
include "ssdomg.mm"
include "ax-mp.mm"
include "simprd.mm"
include "domtr.mm"
include "syl2anr.mm"
include "endomtr.mm"
include "ex.mm"
include "sylbird.mm"
include "mt3i.mm"
include "ssrdv.mm"
include "rgen.mm"
include "iscard2.mm"
include "mpbir2an.mm"

theorem harcard
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( card ` ( har ` A ) ) = ( har ` A )

  proof
    cA
    char
    cfv
    #
    ccrd
    cfv
    @0
    wceq
    @0
    con0
    wcel
    @0
    vx
    cv
    #
    cen
    wbr
    #
    @0
    @1
    wss
    #
    wi
    #
    vx
    con0
    wral
    cA
    harcl
    @4
    vx
    con0
    @1
    con0
    wcel
    #
    @2
    @3
    @5
    @2
    wa
    #
    vy
    @0
    @1
    @6
    vy
    cv
    #
    @0
    wcel
    #
    @7
    @1
    wcel
    #
    @6
    @8
    wa
    #
    @9
    @0
    cA
    cdom
    wbr
    #
    cA
    harndom
    @10
    @9
    wn
    #
    @1
    @7
    wss
    #
    @11
    @10
    @5
    @7
    con0
    wcel
    #
    @13
    @12
    wb
    @5
    @2
    @8
    simpll
    @10
    @14
    @7
    cA
    cdom
    wbr
    #
    @10
    @8
    @14
    @15
    wa
    @6
    @8
    simpr
    cA
    @7
    elharval
    sylib
    #
    simpld
    @1
    @7
    ontri1
    syl2anc
    @10
    @13
    @11
    @10
    @13
    wa
    @2
    @1
    cA
    cdom
    wbr
    #
    @11
    @5
    @2
    @8
    @13
    simpllr
    @13
    @1
    @7
    cdom
    wbr
    #
    @15
    @17
    @10
    @7
    cvv
    wcel
    @13
    @18
    wi
    vy
    vex
    @1
    @7
    cvv
    ssdomg
    ax-mp
    @10
    @14
    @15
    @16
    simprd
    @1
    @7
    cA
    domtr
    syl2anr
    @0
    @1
    cA
    endomtr
    syl2anc
    ex
    sylbird
    mt3i
    ex
    ssrdv
    ex
    rgen
    vx
    @0
    iscard2
    mpbir2an
end
