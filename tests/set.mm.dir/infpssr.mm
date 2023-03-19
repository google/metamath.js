include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wex.mm"
include "wpss.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "cdom.mm"
include "pssnel.mm"
include "adantr.mm"
include "wi.mm"
include "cdif.mm"
include "eldif.mm"
include "wss.mm"
include "pssss.mm"
include "wf1o.mm"
include "bren.mm"
include "cvv.mm"
include "crn.mm"
include "wfo.mm"
include "wceq.mm"
include "simpr.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "vex.mm"
include "rnex.mm"
include "syl6eqelr.mm"
include "ccnv.mm"
include "crdg.mm"
include "cres.mm"
include "simplr.mm"
include "simpll.mm"
include "eqid.mm"
include "infpssrlem5.mm"
include "mpd.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "syl5.mm"
include "impd.mm"
include "sylbir.mm"
include "exlimiv.mm"
include "mpcom.mm"

theorem infpssr
  let cA: class A
  let cX: class X
  let vf: setvar f
  let vy: setvar y


  assert |- ( ( X C. A /\ X ~~ A ) -> _om ~<_ A )

  proof
    vy
    cv
    #
    cA
    wcel
    @0
    cX
    wcel
    wn
    wa
    #
    vy
    wex
    #
    cX
    cA
    wpss
    #
    cX
    cA
    cen
    wbr
    #
    wa
    #
    com
    cA
    cdom
    wbr
    #
    @3
    @2
    @4
    vy
    cX
    cA
    pssnel
    adantr
    @1
    @5
    @6
    wi
    #
    vy
    @1
    @0
    cA
    cX
    cdif
    wcel
    #
    @7
    @0
    cA
    cX
    eldif
    @8
    @3
    @4
    @6
    @3
    cX
    cA
    wss
    #
    @8
    @4
    @6
    wi
    #
    cX
    cA
    pssss
    @8
    @9
    @10
    @4
    cX
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @8
    @9
    wa
    #
    @6
    cX
    cA
    vf
    bren
    @13
    @12
    @6
    vf
    @13
    @12
    @6
    @13
    @12
    wa
    #
    cA
    cvv
    wcel
    @6
    @14
    cA
    @11
    crn
    #
    cvv
    @14
    @12
    cX
    cA
    @11
    wfo
    @15
    cA
    wceq
    @13
    @12
    simpr
    #
    cX
    cA
    @11
    f1ofo
    cX
    cA
    @11
    forn
    3syl
    @11
    vf
    vex
    rnex
    syl6eqelr
    @14
    cA
    cX
    @0
    @11
    @11
    ccnv
    @0
    crdg
    com
    cres
    #
    cvv
    @8
    @9
    @12
    simplr
    @16
    @8
    @9
    @12
    simpll
    @17
    eqid
    infpssrlem5
    mpd
    ex
    exlimdv
    syl5bi
    ex
    syl5
    impd
    sylbir
    exlimiv
    mpcom
end
