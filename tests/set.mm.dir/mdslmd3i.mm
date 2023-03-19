include "cmd.mm"
include "wbr.mm"
include "cin.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "chj.mm"
include "co.mm"
include "wi.mm"
include "cch.mm"
include "wral.mm"
include "wcel.mm"
include "w3a.mm"
include "chlej2.mm"
include "ex.mm"
include "mp3an12.mm"
include "impcom.mm"
include "ssrin.mm"
include "syl.mm"
include "adantll.mm"
include "adantr.mm"
include "wceq.mm"
include "ssin.mm"
include "inass.mm"
include "mdi.mm"
include "mp3anl1.mm"
include "mpanl1.mm"
include "ineq1d.mm"
include "syl5eqr.mm"
include "adantrlr.mm"
include "adantrrr.mm"
include "chincli.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "adantrll.mm"
include "adantrrl.mm"
include "eqtrd.mm"
include "ancoms.mm"
include "an32s.mm"
include "sylan2br.mm"
include "adantllr.mm"
include "in12.mm"
include "inidm.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "eqtr2i.mm"
include "syl5eqss.mm"
include "anim12i.mm"
include "eqss.mm"
include "sylibr.mm"
include "oveq2d.mm"
include "ad3antlr.mm"
include "sseqtrd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "mdbr2.mm"
include "mp2an.mm"

theorem mdslmd3i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  assume mdslmd.1: |- A e. CH
  assume mdslmd.2: |- B e. CH
  assume mdslmd.3: |- C e. CH
  assume mdslmd.4: |- D e. CH


  assert |- ( ( ( A MH B /\ ( A i^i B ) MH C ) /\ ( ( A i^i C ) C_ D /\ D C_ A ) ) -> D MH ( B i^i C ) )

  proof
    cA
    cB
    cmd
    wbr
    #
    cA
    cB
    cin
    #
    cC
    cmd
    wbr
    #
    wa
    #
    cA
    cC
    cin
    #
    cD
    wss
    #
    cD
    cA
    wss
    #
    wa
    #
    wa
    #
    vx
    cv
    #
    cB
    cC
    cin
    #
    wss
    #
    @9
    cD
    chj
    co
    #
    @10
    cin
    #
    @9
    cD
    @10
    cin
    #
    chj
    co
    #
    wss
    #
    wi
    #
    vx
    cch
    wral
    #
    cD
    @10
    cmd
    wbr
    #
    @8
    @17
    vx
    cch
    @8
    @9
    cch
    wcel
    #
    wa
    #
    @11
    @16
    @21
    @11
    wa
    #
    @13
    @9
    cA
    chj
    co
    #
    @10
    cin
    #
    @15
    @21
    @13
    @24
    wss
    #
    @11
    @7
    @20
    @25
    @3
    @6
    @20
    @25
    @5
    @6
    @20
    wa
    @12
    @23
    wss
    #
    @25
    @20
    @6
    @26
    cD
    cch
    wcel
    #
    cA
    cch
    wcel
    #
    @20
    @6
    @26
    wi
    mdslmd.4
    mdslmd.1
    @27
    @28
    @20
    w3a
    @6
    @26
    cD
    cA
    @9
    chlej2
    ex
    mp3an12
    impcom
    @12
    @23
    @10
    ssrin
    syl
    adantll
    adantll
    adantr
    @22
    @24
    @9
    cA
    @10
    cin
    #
    chj
    co
    #
    @15
    @3
    @20
    @11
    @24
    @30
    wceq
    #
    @7
    @11
    @3
    @20
    wa
    @9
    cB
    wss
    #
    @9
    cC
    wss
    #
    wa
    #
    @31
    @9
    cB
    cC
    ssin
    @3
    @34
    @20
    @31
    @20
    @3
    @34
    wa
    #
    @31
    @20
    @35
    wa
    @24
    @9
    @1
    chj
    co
    #
    cC
    cin
    #
    @30
    @20
    @3
    @32
    @24
    @37
    wceq
    #
    @33
    @20
    @0
    @32
    @38
    @2
    @20
    @0
    @32
    wa
    #
    wa
    #
    @24
    @23
    cB
    cin
    #
    cC
    cin
    @37
    @23
    cB
    cC
    inass
    @40
    @41
    @36
    cC
    cB
    cch
    wcel
    #
    @20
    @39
    @41
    @36
    wceq
    #
    mdslmd.2
    @28
    @42
    @20
    @39
    @43
    mdslmd.1
    cA
    cB
    @9
    mdi
    mp3anl1
    mpanl1
    ineq1d
    syl5eqr
    adantrlr
    adantrrr
    @20
    @3
    @33
    @37
    @30
    wceq
    #
    @32
    @20
    @2
    @33
    @44
    @0
    @20
    @2
    @33
    wa
    #
    wa
    @37
    @9
    @1
    cC
    cin
    #
    chj
    co
    #
    @30
    cC
    cch
    wcel
    #
    @20
    @45
    @37
    @47
    wceq
    #
    mdslmd.3
    @1
    cch
    wcel
    @48
    @20
    @45
    @49
    cA
    cB
    mdslmd.1
    mdslmd.2
    chincli
    @1
    cC
    @9
    mdi
    mp3anl1
    mpanl1
    @46
    @29
    @9
    chj
    cA
    cB
    cC
    inass
    oveq2i
    syl6eq
    adantrll
    adantrrl
    eqtrd
    ancoms
    an32s
    sylan2br
    adantllr
    @7
    @30
    @15
    wceq
    @3
    @20
    @11
    @7
    @29
    @14
    @9
    chj
    @7
    @29
    @14
    wss
    #
    @14
    @29
    wss
    #
    wa
    @29
    @14
    wceq
    @5
    @50
    @6
    @51
    @5
    @29
    @4
    @10
    cin
    #
    @14
    @52
    cA
    cC
    @10
    cin
    #
    cin
    @29
    cA
    cC
    @10
    inass
    @53
    @10
    cA
    @53
    cB
    cC
    cC
    cin
    #
    cin
    @10
    cC
    cB
    cC
    in12
    @54
    cC
    cB
    cC
    inidm
    ineq2i
    eqtri
    ineq2i
    eqtr2i
    @4
    cD
    @10
    ssrin
    syl5eqss
    cD
    cA
    @10
    ssrin
    anim12i
    @29
    @14
    eqss
    sylibr
    oveq2d
    ad3antlr
    eqtrd
    sseqtrd
    ex
    ralrimiva
    @27
    @10
    cch
    wcel
    @19
    @18
    wb
    mdslmd.4
    cB
    cC
    mdslmd.2
    mdslmd.3
    chincli
    vx
    cD
    @10
    mdbr2
    mp2an
    sylibr
end
