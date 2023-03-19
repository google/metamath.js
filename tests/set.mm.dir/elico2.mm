include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "wa.mm"
include "cico.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "w3a.mm"
include "wb.mm"
include "rexr.mm"
include "elico1.mm"
include "sylan.mm"
include "cmnf.mm"
include "cpnf.mm"
include "mnfxr.mm"
include "a1i.mm"
include "ad2antrr.mm"
include "simpr1.mm"
include "mnflt.mm"
include "simpr2.mm"
include "xrltletrd.mm"
include "simplr.mm"
include "pnfxr.mm"
include "simpr3.mm"
include "pnfge.mm"
include "ad2antlr.mm"
include "xrrebnd.mm"
include "syl.mm"
include "mpbir2and.mm"
include "3jca.mm"
include "ex.mm"
include "3anim1i.mm"
include "impbid1.mm"
include "bitrd.mm"

theorem elico2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR* ) -> ( C e. ( A [,) B ) <-> ( C e. RR /\ A <_ C /\ C < B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cC
    cA
    cB
    cico
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
    clt
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
    @1
    @3
    @7
    wb
    cA
    rexr
    #
    cA
    cB
    cC
    elico1
    sylan
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
    @10
    @1
    @7
    @11
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
    @12
    cC
    cB
    cpnf
    @15
    @0
    @1
    @7
    simplr
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
    cle
    wbr
    @0
    @7
    cB
    pnfge
    ad2antlr
    xrltletrd
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
