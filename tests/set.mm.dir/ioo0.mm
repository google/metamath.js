include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cioo.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "cle.mm"
include "iooval.mm"
include "eqeq1d.mm"
include "wn.mm"
include "wrex.mm"
include "wne.mm"
include "df-ne.mm"
include "rabn0.mm"
include "bitr3i.mm"
include "wi.mm"
include "xrlttr.mm"
include "3com23.mm"
include "3expa.mm"
include "rexlimdva.mm"
include "w3a.mm"
include "cq.mm"
include "qbtwnxr.mm"
include "qre.mm"
include "rexrd.mm"
include "anim1i.mm"
include "reximi2.mm"
include "syl.mm"
include "3expia.mm"
include "impbid.mm"
include "syl5bb.mm"
include "xrltnle.mm"
include "bitrd.mm"
include "con4bid.mm"

theorem ioo0
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( ( A (,) B ) = (/) <-> B <_ A ) )

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
    cioo
    co
    #
    c0
    wceq
    cA
    vx
    cv
    #
    clt
    wbr
    @4
    cB
    clt
    wbr
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
    cle
    wbr
    #
    @2
    @3
    @6
    c0
    vx
    cA
    cB
    iooval
    eqeq1d
    @2
    @7
    @8
    @2
    @7
    wn
    #
    cA
    cB
    clt
    wbr
    #
    @8
    wn
    @9
    @5
    vx
    cxr
    wrex
    #
    @2
    @10
    @9
    @6
    c0
    wne
    @11
    @6
    c0
    df-ne
    @5
    vx
    cxr
    rabn0
    bitr3i
    @2
    @11
    @10
    @2
    @5
    @10
    vx
    cxr
    @0
    @1
    @4
    cxr
    wcel
    #
    @5
    @10
    wi
    #
    @0
    @12
    @1
    @13
    cA
    @4
    cB
    xrlttr
    3com23
    3expa
    rexlimdva
    @0
    @1
    @10
    @11
    @0
    @1
    @10
    w3a
    @5
    vx
    cq
    wrex
    @11
    vx
    cA
    cB
    qbtwnxr
    @5
    @5
    vx
    cq
    cxr
    @4
    cq
    wcel
    #
    @12
    @5
    @14
    @4
    @4
    qre
    rexrd
    anim1i
    reximi2
    syl
    3expia
    impbid
    syl5bb
    cA
    cB
    xrltnle
    bitrd
    con4bid
    bitrd
end
