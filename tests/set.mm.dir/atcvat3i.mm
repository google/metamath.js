include "cat.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wn.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "ccv.mm"
include "wbr.mm"
include "wi.mm"
include "cch.mm"
include "wb.mm"
include "chcv1.mm"
include "mpan.mm"
include "biimpa.mm"
include "ad2ant2lr.mm"
include "atelch.mm"
include "anim12i.mm"
include "chjcom.mm"
include "oveq2d.mm"
include "chjass.mm"
include "mp3an1.mm"
include "ancoms.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "simpl.mm"
include "chjcl.mm"
include "adantl.mm"
include "w3a.mm"
include "chlej2.mm"
include "ex.mm"
include "syl3anc.mm"
include "imp.mm"
include "eqsstrd.mm"
include "chjidm.mm"
include "syl.mm"
include "ad2antlr.mm"
include "sseqtrd.mm"
include "simpr.mm"
include "chub2.mm"
include "mp3anl3.mm"
include "syl21anc.mm"
include "eqssd.mm"
include "sylan.mm"
include "breq2d.mm"
include "adantrl.mm"
include "mpbird.mm"
include "jctil.mm"
include "syl2an.mm"
include "cvexch.mm"
include "sylibrd.mm"
include "chincl.mm"
include "sylancr.mm"
include "atcvat2.mm"
include "expdimp.mm"
include "syld.mm"
include "exp4b.mm"
include "imp4c.mm"

theorem atcvat3i
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  assume atcvat3.1: |- A e. CH


  assert |- ( ( B e. HAtoms /\ C e. HAtoms ) -> ( ( ( -. B = C /\ -. C C_ A ) /\ B C_ ( A vH C ) ) -> ( A i^i ( B vH C ) ) e. HAtoms ) )

  proof
    cB
    cat
    wcel
    #
    cC
    cat
    wcel
    #
    wa
    #
    cB
    cC
    wceq
    wn
    #
    cC
    cA
    wss
    wn
    #
    cB
    cA
    cC
    chj
    co
    #
    wss
    #
    cA
    cB
    cC
    chj
    co
    #
    cin
    #
    cat
    wcel
    #
    @2
    @3
    @4
    @6
    @9
    @2
    @3
    wa
    @4
    @6
    wa
    #
    @8
    @7
    ccv
    wbr
    #
    @9
    @2
    @10
    @11
    wi
    @3
    @2
    @10
    cA
    cA
    @7
    chj
    co
    #
    ccv
    wbr
    #
    @11
    @2
    @10
    @13
    @2
    @10
    wa
    @13
    cA
    @5
    ccv
    wbr
    #
    @1
    @4
    @14
    @0
    @6
    @1
    @4
    @14
    cA
    cch
    wcel
    #
    @1
    @4
    @14
    wb
    atcvat3.1
    cA
    cC
    chcv1
    mpan
    biimpa
    ad2ant2lr
    @2
    @6
    @13
    @14
    wb
    @4
    @2
    @6
    wa
    @12
    @5
    cA
    ccv
    @2
    cB
    cch
    wcel
    #
    cC
    cch
    wcel
    #
    wa
    #
    @6
    @12
    @5
    wceq
    @0
    @16
    @1
    @17
    cB
    atelch
    #
    cC
    atelch
    #
    anim12i
    @18
    @6
    wa
    #
    @12
    @5
    @21
    @12
    @5
    @5
    chj
    co
    #
    @5
    @21
    @12
    @5
    cB
    chj
    co
    #
    @22
    @18
    @12
    @23
    wceq
    @6
    @18
    @12
    cA
    cC
    cB
    chj
    co
    #
    chj
    co
    #
    @23
    @18
    @7
    @24
    cA
    chj
    cB
    cC
    chjcom
    oveq2d
    @17
    @16
    @23
    @25
    wceq
    #
    @15
    @17
    @16
    @26
    atcvat3.1
    cA
    cC
    cB
    chjass
    mp3an1
    ancoms
    eqtr4d
    adantr
    @18
    @6
    @23
    @22
    wss
    #
    @18
    @16
    @5
    cch
    wcel
    #
    @28
    @6
    @27
    wi
    @16
    @17
    simpl
    @17
    @28
    @16
    @15
    @17
    @28
    atcvat3.1
    cA
    cC
    chjcl
    mpan
    #
    adantl
    #
    @30
    @16
    @28
    @28
    w3a
    @6
    @27
    cB
    @5
    @5
    chlej2
    ex
    syl3anc
    imp
    eqsstrd
    @17
    @22
    @5
    wceq
    #
    @16
    @6
    @17
    @28
    @31
    @29
    @5
    chjidm
    syl
    ad2antlr
    sseqtrd
    @18
    @5
    @12
    wss
    #
    @6
    @18
    @17
    @7
    cch
    wcel
    #
    cC
    @7
    wss
    #
    @32
    @16
    @17
    simpr
    cB
    cC
    chjcl
    #
    @17
    @16
    @34
    cC
    cB
    chub2
    ancoms
    @17
    @33
    @15
    @34
    @32
    atcvat3.1
    cC
    @7
    cA
    chlej2
    mp3anl3
    syl21anc
    adantr
    eqssd
    sylan
    breq2d
    adantrl
    mpbird
    ex
    @2
    @15
    @33
    wa
    #
    @11
    @13
    wb
    @0
    @16
    @17
    @36
    @1
    @19
    @20
    @18
    @33
    @15
    @35
    atcvat3.1
    jctil
    syl2an
    cA
    @7
    cvexch
    syl
    sylibrd
    adantr
    @2
    @3
    @11
    @9
    @2
    @8
    cch
    wcel
    #
    @0
    @1
    @3
    @11
    wa
    @9
    wi
    @0
    @16
    @17
    @37
    @1
    @19
    @20
    @18
    @15
    @33
    @37
    atcvat3.1
    @35
    cA
    @7
    chincl
    sylancr
    syl2an
    @0
    @1
    simpl
    @0
    @1
    simpr
    @8
    cB
    cC
    atcvat2
    syl3anc
    expdimp
    syld
    exp4b
    imp4c
end
