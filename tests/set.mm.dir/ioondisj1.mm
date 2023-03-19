include "cxr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "cle.mm"
include "cioo.mm"
include "co.mm"
include "cin.mm"
include "cif.mm"
include "c0.mm"
include "wceq.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simplr1.mm"
include "simplr2.mm"
include "iooin.mm"
include "syl22anc.mm"
include "simprl.mm"
include "iftrued.mm"
include "oveq1d.mm"
include "wne.mm"
include "simprr.mm"
include "simplr3.mm"
include "jca.mm"
include "wb.mm"
include "xrltmin.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "ifcld.mm"
include "ioon0.mm"
include "syl2anc.mm"
include "eqnetrd.mm"

theorem ioondisj1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( ( A e. RR* /\ B e. RR* /\ A < B ) /\ ( C e. RR* /\ D e. RR* /\ C < D ) ) /\ ( A <_ C /\ C < B ) ) -> ( ( A (,) B ) i^i ( C (,) D ) ) =/= (/) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    w3a
    #
    cC
    cxr
    wcel
    #
    cD
    cxr
    wcel
    #
    cC
    cD
    clt
    wbr
    #
    w3a
    #
    wa
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
    wa
    #
    wa
    #
    cA
    cB
    cioo
    co
    cC
    cD
    cioo
    co
    cin
    #
    @9
    cC
    cA
    cif
    #
    cB
    cD
    cle
    wbr
    #
    cB
    cD
    cif
    #
    cioo
    co
    #
    c0
    @12
    @0
    @1
    @4
    @5
    @13
    @17
    wceq
    @0
    @1
    @2
    @7
    @11
    simpll1
    @0
    @1
    @2
    @7
    @11
    simpll2
    #
    @4
    @5
    @6
    @3
    @11
    simplr1
    #
    @4
    @5
    @6
    @3
    @11
    simplr2
    #
    cA
    cB
    cC
    cD
    iooin
    syl22anc
    @12
    @17
    cC
    @16
    cioo
    co
    #
    c0
    @12
    @14
    cC
    @16
    cioo
    @12
    @9
    cC
    cA
    @8
    @9
    @10
    simprl
    iftrued
    oveq1d
    @12
    @21
    c0
    wne
    #
    cC
    @16
    clt
    wbr
    #
    @12
    @23
    @10
    @6
    wa
    #
    @12
    @10
    @6
    @8
    @9
    @10
    simprr
    @4
    @5
    @6
    @3
    @11
    simplr3
    jca
    @12
    @4
    @1
    @5
    @23
    @24
    wb
    @19
    @18
    @20
    cC
    cB
    cD
    xrltmin
    syl3anc
    mpbird
    @12
    @4
    @16
    cxr
    wcel
    @22
    @23
    wb
    @19
    @12
    @15
    cB
    cD
    cxr
    @18
    @20
    ifcld
    cC
    @16
    ioon0
    syl2anc
    mpbird
    eqnetrd
    eqnetrd
end
