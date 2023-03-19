include "cun.mm"
include "cesum.mm"
include "cxad.mm"
include "co.mm"
include "cvv.mm"
include "nfun.mm"
include "wcel.mm"
include "unexg.mm"
include "syl2anc.mm"
include "cv.mm"
include "wo.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "elun.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "cmpt.mm"
include "cxrs.mm"
include "cress.mm"
include "xrge0base.mm"
include "xrge0plusg.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "a1i.mm"
include "ctmd.mm"
include "xrge0tmd.mm"
include "nfcv.mm"
include "eqid.mm"
include "fmptdF.mm"
include "ctsu.mm"
include "cres.mm"
include "esumel.mm"
include "wss.mm"
include "wceq.mm"
include "ssun1.mm"
include "resmptf.mm"
include "mp1i.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "ssun2.mm"
include "eqidd.mm"
include "tsmssplit.mm"
include "esumid.mm"

theorem esumsplit
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume esumsplit.1: |- F/ k ph
  assume esumsplit.2: |- F/_ k A
  assume esumsplit.3: |- F/_ k B
  assume esumsplit.4: |- ( ph -> A e. _V )
  assume esumsplit.5: |- ( ph -> B e. _V )
  assume esumsplit.6: |- ( ph -> ( A i^i B ) = (/) )
  assume esumsplit.7: |- ( ( ph /\ k e. A ) -> C e. ( 0 [,] +oo ) )
  assume esumsplit.8: |- ( ( ph /\ k e. B ) -> C e. ( 0 [,] +oo ) )


  assert |- ( ph -> sum* k e. ( A u. B ) C = ( sum* k e. A C +e sum* k e. B C ) )

  proof
    wph
    cA
    cB
    cun
    #
    cC
    cA
    cC
    vk
    cesum
    #
    cB
    cC
    vk
    cesum
    #
    cxad
    co
    vk
    cvv
    esumsplit.1
    vk
    cA
    cB
    esumsplit.2
    esumsplit.3
    nfun
    #
    wph
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    @0
    cvv
    wcel
    esumsplit.4
    esumsplit.5
    cA
    cB
    cvv
    cvv
    unexg
    syl2anc
    #
    vk
    cv
    #
    @0
    wcel
    wph
    @5
    cA
    wcel
    #
    @5
    cB
    wcel
    #
    wo
    cC
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @5
    cA
    cB
    elun
    wph
    @6
    @9
    @7
    esumsplit.7
    esumsplit.8
    jaodan
    sylan2b
    #
    wph
    @0
    @8
    cA
    cB
    cxad
    vk
    @0
    cC
    cmpt
    #
    cxrs
    @8
    cress
    co
    #
    cvv
    @1
    @2
    xrge0base
    xrge0plusg
    @12
    ccmn
    wcel
    wph
    xrge0cmn
    a1i
    @12
    ctmd
    wcel
    wph
    xrge0tmd
    a1i
    @4
    wph
    vk
    @0
    cC
    @8
    @11
    esumsplit.1
    @3
    vk
    @8
    nfcv
    @10
    @11
    eqid
    fmptdF
    wph
    @1
    @12
    vk
    cA
    cC
    cmpt
    #
    ctsu
    co
    @12
    @11
    cA
    cres
    #
    ctsu
    co
    wph
    cA
    cC
    vk
    cvv
    esumsplit.1
    esumsplit.2
    esumsplit.4
    esumsplit.7
    esumel
    wph
    @14
    @13
    @12
    ctsu
    cA
    @0
    wss
    @14
    @13
    wceq
    wph
    cA
    cB
    ssun1
    vk
    @0
    cA
    cC
    @3
    esumsplit.2
    resmptf
    mp1i
    oveq2d
    eleqtrrd
    wph
    @2
    @12
    vk
    cB
    cC
    cmpt
    #
    ctsu
    co
    @12
    @11
    cB
    cres
    #
    ctsu
    co
    wph
    cB
    cC
    vk
    cvv
    esumsplit.1
    esumsplit.3
    esumsplit.5
    esumsplit.8
    esumel
    wph
    @16
    @15
    @12
    ctsu
    cB
    @0
    wss
    @16
    @15
    wceq
    wph
    cB
    cA
    ssun2
    vk
    @0
    cB
    cC
    @3
    esumsplit.3
    resmptf
    mp1i
    oveq2d
    eleqtrrd
    esumsplit.6
    wph
    @0
    eqidd
    tsmssplit
    esumid
end
