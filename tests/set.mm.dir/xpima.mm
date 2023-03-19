include "cxp.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "exmid.mm"
include "crn.mm"
include "cvv.mm"
include "cres.mm"
include "df-ima.mm"
include "df-res.mm"
include "rneqi.mm"
include "eqtri.mm"
include "inxp.mm"
include "inv1.mm"
include "xpeq2i.mm"
include "3eqtri.mm"
include "xpeq1.mm"
include "0xp.mm"
include "syl6eq.mm"
include "rneqd.mm"
include "rn0.mm"
include "syl5eq.mm"
include "ancli.mm"
include "wne.mm"
include "df-ne.mm"
include "rnxp.mm"
include "sylbir.mm"
include "orim12i.mm"
include "ax-mp.mm"
include "eqif.mm"
include "mpbir.mm"

theorem xpima
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A X. B ) " C ) = if ( ( A i^i C ) = (/) , (/) , B )

  proof
    cA
    cB
    cxp
    #
    cC
    cima
    #
    cA
    cC
    cin
    #
    c0
    wceq
    #
    c0
    cB
    cif
    wceq
    @3
    @1
    c0
    wceq
    #
    wa
    #
    @3
    wn
    #
    @1
    cB
    wceq
    #
    wa
    #
    wo
    #
    @3
    @6
    wo
    @9
    @3
    exmid
    @3
    @5
    @6
    @8
    @3
    @4
    @3
    @1
    @2
    cB
    cxp
    #
    crn
    #
    c0
    @1
    @0
    cC
    cvv
    cxp
    cin
    #
    crn
    #
    @2
    cB
    cvv
    cin
    #
    cxp
    #
    crn
    @11
    @1
    @0
    cC
    cres
    #
    crn
    @13
    @0
    cC
    df-ima
    @16
    @12
    @0
    cC
    df-res
    rneqi
    eqtri
    @12
    @15
    cA
    cB
    cC
    cvv
    inxp
    rneqi
    @15
    @10
    @14
    cB
    @2
    cB
    inv1
    xpeq2i
    rneqi
    3eqtri
    #
    @3
    @11
    c0
    crn
    c0
    @3
    @10
    c0
    @3
    @10
    c0
    cB
    cxp
    c0
    @2
    c0
    cB
    xpeq1
    cB
    0xp
    syl6eq
    rneqd
    rn0
    syl6eq
    syl5eq
    ancli
    @6
    @7
    @6
    @1
    @11
    cB
    @17
    @6
    @2
    c0
    wne
    @11
    cB
    wceq
    @2
    c0
    df-ne
    @2
    cB
    rnxp
    sylbir
    syl5eq
    ancli
    orim12i
    ax-mp
    @3
    @1
    c0
    cB
    eqif
    mpbir
end
