include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cicc.mm"
include "co.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wb.mm"
include "rexr.mm"
include "elicc1.mm"
include "syl2an.mm"
include "cmnf.mm"
include "clt.mm"
include "cpnf.mm"
include "mnfxr.mm"
include "a1i.mm"
include "ad2antrr.mm"
include "simpr1.mm"
include "mnflt.mm"
include "simpr2.mm"
include "xrltletrd.mm"
include "ad2antlr.mm"
include "pnfxr.mm"
include "simpr3.mm"
include "ltpnf.mm"
include "xrlelttrd.mm"
include "xrrebnd.mm"
include "syl.mm"
include "mpbir2and.mm"
include "3jca.mm"
include "ex.mm"
include "3anim1i.mm"
include "impbid1.mm"
include "bitrd.mm"

theorem elicc2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR ) -> ( C e. ( A [,] B ) <-> ( C e. RR /\ A <_ C /\ C <_ B ) ) )

  proof
    cA
    cr
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
    cicc
    co
    wcel
    #
    cC
    cxr
    wcel
    #
    cA
    cC
    cle
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
    @0
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @3
    @7
    wb
    @1
    cA
    rexr
    #
    cB
    rexr
    #
    cA
    cB
    cC
    elicc1
    syl2an
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
    @14
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
    @14
    cmnf
    cA
    cC
    cmnf
    cxr
    wcel
    @14
    mnfxr
    a1i
    @0
    @10
    @1
    @7
    @12
    ad2antrr
    @2
    @4
    @5
    @6
    simpr1
    #
    @0
    cmnf
    cA
    clt
    wbr
    @1
    @7
    cA
    mnflt
    ad2antrr
    @2
    @4
    @5
    @6
    simpr2
    #
    xrltletrd
    @14
    cC
    cB
    cpnf
    @17
    @1
    @11
    @0
    @7
    @13
    ad2antlr
    cpnf
    cxr
    wcel
    @14
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
    @14
    @4
    @8
    @15
    @16
    wa
    wb
    @17
    cC
    xrrebnd
    syl
    mpbir2and
    @18
    @19
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
