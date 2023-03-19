include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cioc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "wb.mm"
include "rexr.mm"
include "elioc1.mm"
include "sylan2.mm"
include "cmnf.mm"
include "cpnf.mm"
include "mnfxr.mm"
include "a1i.mm"
include "simpll.mm"
include "simpr1.mm"
include "mnfle.mm"
include "ad2antrr.mm"
include "simpr2.mm"
include "xrlelttrd.mm"
include "ad2antlr.mm"
include "pnfxr.mm"
include "simpr3.mm"
include "ltpnf.mm"
include "xrrebnd.mm"
include "syl.mm"
include "mpbir2and.mm"
include "3jca.mm"
include "ex.mm"
include "3anim1i.mm"
include "impbid1.mm"
include "bitrd.mm"

theorem elioc2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR ) -> ( C e. ( A (,] B ) <-> ( C e. RR /\ A < C /\ C <_ B ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cC
    cA
    cB
    cioc
    co
    wcel
    #
    cC
    cxr
    wcel
    #
    cA
    cC
    clt
    wbr
    #
    cC
    cB
    cle
    wbr
    #
    w3a
    #
    cC
    cr
    wcel
    #
    @5
    @6
    w3a
    #
    @1
    @0
    cB
    cxr
    wcel
    #
    @3
    @7
    wb
    cB
    rexr
    #
    cA
    cB
    cC
    elioc1
    sylan2
    @2
    @7
    @9
    @2
    @7
    @9
    @2
    @7
    wa
    #
    @8
    @5
    @6
    @12
    @8
    cmnf
    cC
    clt
    wbr
    #
    cC
    cpnf
    clt
    wbr
    #
    @12
    cmnf
    cA
    cC
    cmnf
    cxr
    wcel
    @12
    mnfxr
    a1i
    @0
    @1
    @7
    simpll
    @2
    @4
    @5
    @6
    simpr1
    #
    @0
    cmnf
    cA
    cle
    wbr
    @1
    @7
    cA
    mnfle
    ad2antrr
    @2
    @4
    @5
    @6
    simpr2
    #
    xrlelttrd
    @12
    cC
    cB
    cpnf
    @15
    @1
    @10
    @0
    @7
    @11
    ad2antlr
    cpnf
    cxr
    wcel
    @12
    pnfxr
    a1i
    @2
    @4
    @5
    @6
    simpr3
    #
    @1
    cB
    cpnf
    clt
    wbr
    @0
    @7
    cB
    ltpnf
    ad2antlr
    xrlelttrd
    @12
    @4
    @8
    @13
    @14
    wa
    wb
    @15
    cC
    xrrebnd
    syl
    mpbir2and
    @16
    @17
    3jca
    ex
    @8
    @4
    @5
    @6
    cC
    rexr
    3anim1i
    impbid1
    bitrd
end
