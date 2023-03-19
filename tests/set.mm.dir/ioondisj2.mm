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
include "simprr.mm"
include "xrmineq.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "wne.mm"
include "simpr.mm"
include "iftrued.mm"
include "simplr3.mm"
include "adantr.mm"
include "eqbrtrd.mm"
include "wn.mm"
include "iffalsed.mm"
include "simplrl.mm"
include "pm2.61dan.mm"
include "wb.mm"
include "ifcld.mm"
include "ioon0.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "eqnetrd.mm"

theorem ioondisj2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( ( A e. RR* /\ B e. RR* /\ A < B ) /\ ( C e. RR* /\ D e. RR* /\ C < D ) ) /\ ( A < D /\ D <_ B ) ) -> ( ( A (,) B ) i^i ( C (,) D ) ) =/= (/) )

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
    cD
    clt
    wbr
    #
    cD
    cB
    cle
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
    cA
    cC
    cle
    wbr
    #
    cC
    cA
    cif
    #
    cB
    cD
    cle
    wbr
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
    #
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
    @15
    cD
    cioo
    co
    #
    c0
    @12
    @16
    cD
    @15
    cioo
    @12
    @1
    @5
    @10
    @16
    cD
    wceq
    @19
    @21
    @8
    @9
    @10
    simprr
    cB
    cD
    xrmineq
    syl3anc
    oveq2d
    @12
    @22
    c0
    wne
    #
    @15
    cD
    clt
    wbr
    #
    @12
    @14
    @24
    @12
    @14
    wa
    #
    @15
    cC
    cD
    clt
    @25
    @14
    cC
    cA
    @12
    @14
    simpr
    iftrued
    @12
    @6
    @14
    @4
    @5
    @6
    @3
    @11
    simplr3
    adantr
    eqbrtrd
    @12
    @14
    wn
    #
    wa
    #
    @15
    cA
    cD
    clt
    @27
    @14
    cC
    cA
    @12
    @26
    simpr
    iffalsed
    @8
    @9
    @10
    @26
    simplrl
    eqbrtrd
    pm2.61dan
    @12
    @15
    cxr
    wcel
    @5
    @23
    @24
    wb
    @12
    @14
    cC
    cA
    cxr
    @20
    @18
    ifcld
    @21
    @15
    cD
    ioon0
    syl2anc
    mpbird
    eqnetrd
    eqnetrd
end
