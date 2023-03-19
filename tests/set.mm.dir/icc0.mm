include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cicc.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "clt.mm"
include "iccval.mm"
include "eqeq1d.mm"
include "wn.mm"
include "wrex.mm"
include "wne.mm"
include "df-ne.mm"
include "rabn0.mm"
include "bitr3i.mm"
include "wi.mm"
include "xrletr.mm"
include "3com23.mm"
include "3expa.mm"
include "rexlimdva.mm"
include "w3a.mm"
include "simp2.mm"
include "simp3.mm"
include "xrleid.mm"
include "3ad2ant2.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "3expia.mm"
include "impbid.mm"
include "syl5bb.mm"
include "xrlenlt.mm"
include "bitrd.mm"
include "con4bid.mm"

theorem icc0
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( ( A [,] B ) = (/) <-> B < A ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cB
    cicc
    co
    #
    c0
    wceq
    cA
    vx
    cv
    #
    cle
    wbr
    #
    @4
    cB
    cle
    wbr
    #
    wa
    #
    vx
    cxr
    crab
    #
    c0
    wceq
    #
    cB
    cA
    clt
    wbr
    #
    @2
    @3
    @8
    c0
    vx
    cA
    cB
    iccval
    eqeq1d
    @2
    @9
    @10
    @2
    @9
    wn
    #
    cA
    cB
    cle
    wbr
    #
    @10
    wn
    @11
    @7
    vx
    cxr
    wrex
    #
    @2
    @12
    @11
    @8
    c0
    wne
    @13
    @8
    c0
    df-ne
    @7
    vx
    cxr
    rabn0
    bitr3i
    @2
    @13
    @12
    @2
    @7
    @12
    vx
    cxr
    @0
    @1
    @4
    cxr
    wcel
    #
    @7
    @12
    wi
    #
    @0
    @14
    @1
    @15
    cA
    @4
    cB
    xrletr
    3com23
    3expa
    rexlimdva
    @0
    @1
    @12
    @13
    @0
    @1
    @12
    w3a
    @1
    @12
    cB
    cB
    cle
    wbr
    #
    @13
    @0
    @1
    @12
    simp2
    @0
    @1
    @12
    simp3
    @1
    @0
    @16
    @12
    cB
    xrleid
    3ad2ant2
    @7
    @12
    @16
    wa
    vx
    cB
    cxr
    @4
    cB
    wceq
    @5
    @12
    @6
    @16
    @4
    cB
    cA
    cle
    breq2
    @4
    cB
    cB
    cle
    breq1
    anbi12d
    rspcev
    syl12anc
    3expia
    impbid
    syl5bb
    cA
    cB
    xrlenlt
    bitrd
    con4bid
    bitrd
end
