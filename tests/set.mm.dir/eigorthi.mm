include "cfv.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "csp.mm"
include "ccj.mm"
include "cmul.mm"
include "wne.mm"
include "cc0.mm"
include "oveq2.mm"
include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "his5.mm"
include "mp3an.mm"
include "syl6eq.mm"
include "oveq1.mm"
include "ax-his3.mm"
include "eqeqan12rd.mm"
include "wb.mm"
include "hicli.mm"
include "cjcli.mm"
include "mulcan2.mm"
include "mp3an12.mm"
include "mpan.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "biimpcd.mm"
include "necon1d.mm"
include "com12.mm"
include "mul01i.mm"
include "eqtr4i.mm"
include "eqtr4d.mm"
include "impbid1.mm"
include "sylan9bb.mm"

theorem eigorthi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  assume eigorthi.1: |- A e. ~H
  assume eigorthi.2: |- B e. ~H
  assume eigorthi.3: |- C e. CC
  assume eigorthi.4: |- D e. CC


  assert |- ( ( ( ( T ` A ) = ( C .h A ) /\ ( T ` B ) = ( D .h B ) ) /\ C =/= ( * ` D ) ) -> ( ( A .ih ( T ` B ) ) = ( ( T ` A ) .ih B ) <-> ( A .ih B ) = 0 ) )

  proof
    cA
    cT
    cfv
    #
    cC
    cA
    csm
    co
    #
    wceq
    #
    cB
    cT
    cfv
    #
    cD
    cB
    csm
    co
    #
    wceq
    #
    wa
    cA
    @3
    csp
    co
    #
    @0
    cB
    csp
    co
    #
    wceq
    cD
    ccj
    cfv
    #
    cA
    cB
    csp
    co
    #
    cmul
    co
    #
    cC
    @9
    cmul
    co
    #
    wceq
    #
    cC
    @8
    wne
    #
    @9
    cc0
    wceq
    #
    @5
    @2
    @6
    @10
    @7
    @11
    @5
    @6
    cA
    @4
    csp
    co
    #
    @10
    @3
    @4
    cA
    csp
    oveq2
    cD
    cc
    wcel
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    @15
    @10
    wceq
    eigorthi.4
    eigorthi.1
    eigorthi.2
    cD
    cA
    cB
    his5
    mp3an
    syl6eq
    @2
    @7
    @1
    cB
    csp
    co
    #
    @11
    @0
    @1
    cB
    csp
    oveq1
    cC
    cc
    wcel
    #
    @16
    @17
    @18
    @11
    wceq
    eigorthi.3
    eigorthi.1
    eigorthi.2
    cC
    cA
    cB
    ax-his3
    mp3an
    syl6eq
    eqeqan12rd
    @13
    @12
    @14
    @12
    @13
    @14
    @12
    @9
    cc0
    cC
    @8
    @9
    cc0
    wne
    #
    @12
    cC
    @8
    wceq
    #
    @20
    @12
    @8
    cC
    wceq
    #
    @21
    @9
    cc
    wcel
    #
    @20
    @12
    @22
    wb
    #
    cA
    cB
    eigorthi.1
    eigorthi.2
    hicli
    @8
    cc
    wcel
    @19
    @23
    @20
    wa
    @24
    cD
    eigorthi.4
    cjcli
    #
    eigorthi.3
    @8
    cC
    @9
    mulcan2
    mp3an12
    mpan
    @8
    cC
    eqcom
    syl6bb
    biimpcd
    necon1d
    com12
    @14
    @10
    @8
    cc0
    cmul
    co
    #
    @11
    @9
    cc0
    @8
    cmul
    oveq2
    @14
    @11
    cC
    cc0
    cmul
    co
    #
    @26
    @9
    cc0
    cC
    cmul
    oveq2
    @27
    cc0
    @26
    cC
    eigorthi.3
    mul01i
    @8
    @25
    mul01i
    eqtr4i
    syl6eq
    eqtr4d
    impbid1
    sylan9bb
end
