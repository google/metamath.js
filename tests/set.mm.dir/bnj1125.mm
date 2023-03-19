include "w-bnj15.mm"
include "wcel.mm"
include "c-bnj18.mm"
include "w3a.mm"
include "cvv.mm"
include "w-bnj19.mm"
include "c-bnj14.mm"
include "wss.mm"
include "simp1.mm"
include "bnj1127.mm"
include "3ad2ant3.mm"
include "bnj893.mm"
include "3adant3.mm"
include "bnj1029.mm"
include "simp3.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wi.mm"
include "elisset.mm"
include "wral.mm"
include "df-bnj19.mm"
include "rsp.mm"
include "sylbi.mm"
include "syl.mm"
include "eleq1.mm"
include "bnj602.mm"
include "sseq1d.mm"
include "imbi12d.mm"
include "syl5ib.mm"
include "exlimiv.mm"
include "mpcom.mm"
include "mpd.mm"
include "wa.mm"
include "biid.mm"
include "bnj1124.mm"
include "syl23anc.mm"

theorem bnj1125
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  let vy: setvar y


  assert |- ( ( R _FrSe A /\ X e. A /\ Y e. _trCl ( X , A , R ) ) -> _trCl ( Y , A , R ) C_ _trCl ( X , A , R ) )

  proof
    cA
    cR
    w-bnj15
    #
    cX
    cA
    wcel
    #
    cY
    cA
    cR
    cX
    c-bnj18
    #
    wcel
    #
    w3a
    #
    @0
    cY
    cA
    wcel
    #
    @2
    cvv
    wcel
    #
    cA
    @2
    cR
    w-bnj19
    #
    cA
    cR
    cY
    c-bnj14
    #
    @2
    wss
    #
    cA
    cR
    cY
    c-bnj18
    @2
    wss
    @0
    @1
    @3
    simp1
    @3
    @0
    @5
    @1
    cA
    cR
    cX
    cY
    bnj1127
    3ad2ant3
    @0
    @1
    @6
    @3
    cA
    cR
    cX
    bnj893
    3adant3
    @0
    @1
    @7
    @3
    cA
    cR
    cX
    bnj1029
    3adant3
    #
    @4
    @3
    @9
    @0
    @1
    @3
    simp3
    vy
    cv
    #
    cY
    wceq
    #
    vy
    wex
    #
    @4
    @3
    @9
    wi
    #
    @3
    @0
    @13
    @1
    vy
    cY
    @2
    elisset
    3ad2ant3
    @12
    @4
    @14
    wi
    vy
    @4
    @11
    @2
    wcel
    #
    cA
    cR
    @11
    c-bnj14
    #
    @2
    wss
    #
    wi
    #
    @12
    @14
    @4
    @7
    @18
    @10
    @7
    @17
    vy
    @2
    wral
    @18
    vy
    cA
    @2
    cR
    df-bnj19
    @17
    vy
    @2
    rsp
    sylbi
    syl
    @12
    @15
    @3
    @17
    @9
    @11
    cY
    @2
    eleq1
    @12
    @16
    @8
    @2
    cA
    cR
    @11
    cY
    bnj602
    sseq1d
    imbi12d
    syl5ib
    exlimiv
    mpcom
    mpd
    @0
    @5
    wa
    #
    @6
    @7
    @9
    w3a
    #
    cA
    @2
    cR
    cY
    @19
    biid
    @20
    biid
    bnj1124
    syl23anc
end
