include "cat.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wss.mm"
include "c0h.mm"
include "wne.mm"
include "chj.mm"
include "co.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "hatomici.mm"
include "cch.mm"
include "atelch.mm"
include "chub1.mm"
include "syl2an.mm"
include "sseq1.mm"
include "syl5ibr.mm"
include "expd.mm"
include "impcom.mm"
include "anim2d.mm"
include "expcomd.mm"
include "reximdvai.mm"
include "syl5.mm"
include "ex.mm"
include "a1i.mm"
include "com4l.mm"
include "imp4a.mm"
include "adantl.mm"
include "wb.mm"
include "chlejb2.mm"
include "mpan2.mm"
include "biimpa.mm"
include "sseq2d.mm"
include "expl.mm"
include "chub2.mm"
include "jctird.mm"
include "simpl.mm"
include "jctild.mm"
include "impl.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl.mm"
include "adantrl.mm"
include "exp31.mm"
include "wo.mm"
include "wn.mm"
include "simpr.mm"
include "ioran.mm"
include "cin.mm"
include "atcvat3i.mm"
include "w3a.mm"
include "ad2antlr.mm"
include "imp.mm"
include "simpll.mm"
include "3jca.mm"
include "inss2.mm"
include "chjcom.mm"
include "syl5sseq.mm"
include "adantr.mm"
include "atnssm0.mm"
include "mpan.mm"
include "inss1.mm"
include "sslin.mm"
include "ax-mp.mm"
include "incom.mm"
include "sseqtri.mm"
include "sseq2.mm"
include "mpbii.mm"
include "chjcl.mm"
include "chincl.mm"
include "sylancr.mm"
include "syl2anc.mm"
include "chle0.mm"
include "syl5ib.mm"
include "sylbid.mm"
include "adantrr.mm"
include "jca.mm"
include "atexch.mm"
include "sylc.mm"
include "jctil.mm"
include "jcad.mm"
include "syl6.mm"
include "syl5bi.mm"
include "syl7.mm"
include "ecase3d.mm"

theorem atcvat4i
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume atcvat3.1: |- A e. CH

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( ( B e. HAtoms /\ C e. HAtoms ) -> ( ( A =/= 0H /\ B C_ ( A vH C ) ) -> E. x e. HAtoms ( x C_ A /\ B C_ ( C vH x ) ) ) )

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
    #
    cC
    cA
    wss
    #
    cA
    c0h
    wne
    #
    cB
    cA
    cC
    chj
    co
    #
    wss
    #
    wa
    #
    vx
    cv
    #
    cA
    wss
    #
    cB
    cC
    @9
    chj
    co
    #
    wss
    #
    wa
    #
    vx
    cat
    wrex
    #
    wi
    #
    @1
    @3
    @15
    wi
    @0
    @1
    @3
    @5
    @7
    @14
    @7
    @1
    @3
    @5
    @14
    @1
    @3
    @5
    @14
    wi
    #
    wi
    wi
    @7
    @1
    @3
    @16
    @5
    @10
    vx
    cat
    wrex
    @1
    @3
    wa
    #
    @14
    vx
    cA
    atcvat3.1
    hatomici
    @17
    @10
    @13
    vx
    cat
    @17
    @10
    @9
    cat
    wcel
    #
    @13
    @17
    @18
    @12
    @10
    @3
    @1
    @18
    @12
    wi
    @3
    @1
    @18
    @12
    @1
    @18
    wa
    @12
    @3
    cC
    @11
    wss
    #
    @1
    cC
    cch
    wcel
    #
    @9
    cch
    wcel
    @19
    @18
    cC
    atelch
    #
    @9
    atelch
    cC
    @9
    chub1
    syl2an
    cB
    cC
    @11
    sseq1
    syl5ibr
    expd
    impcom
    anim2d
    expcomd
    reximdvai
    syl5
    ex
    a1i
    com4l
    imp4a
    adantl
    @2
    @4
    @8
    @14
    @2
    @4
    wa
    #
    @7
    @14
    @5
    @22
    @7
    wa
    @0
    cB
    cA
    wss
    #
    cB
    cC
    cB
    chj
    co
    #
    wss
    #
    wa
    #
    wa
    #
    @14
    @2
    @4
    @7
    @27
    @2
    @4
    @7
    wa
    #
    @26
    @0
    @0
    cB
    cch
    wcel
    #
    @20
    @28
    @26
    wi
    @1
    cB
    atelch
    #
    @21
    @29
    @20
    wa
    #
    @28
    @23
    @25
    @20
    @28
    @23
    wi
    @29
    @20
    @4
    @7
    @23
    @20
    @4
    wa
    #
    @7
    @23
    @32
    @6
    cA
    cB
    @20
    @4
    @6
    cA
    wceq
    #
    @20
    cA
    cch
    wcel
    #
    @4
    @33
    wb
    atcvat3.1
    cC
    cA
    chlejb2
    mpan2
    biimpa
    sseq2d
    biimpa
    expl
    adantl
    cB
    cC
    chub2
    jctird
    syl2an
    @0
    @1
    simpl
    jctild
    impl
    @13
    @26
    vx
    cB
    cat
    @9
    cB
    wceq
    #
    @10
    @23
    @12
    @25
    @9
    cB
    cA
    sseq1
    @35
    @11
    @24
    cB
    @9
    cB
    cC
    chj
    oveq2
    sseq2d
    anbi12d
    rspcev
    syl
    adantrl
    exp31
    @8
    @7
    @2
    @3
    @4
    wo
    wn
    #
    @14
    @5
    @7
    simpr
    @36
    @3
    wn
    #
    @4
    wn
    #
    wa
    #
    @2
    @7
    @14
    wi
    @3
    @4
    ioran
    @2
    @39
    @7
    @14
    @2
    @39
    @7
    wa
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
    @42
    cA
    wss
    #
    cB
    cC
    @42
    chj
    co
    #
    wss
    #
    wa
    #
    wa
    @14
    @2
    @40
    @43
    @47
    cA
    cB
    cC
    atcvat3.1
    atcvat3i
    #
    @2
    @40
    @47
    @2
    @40
    wa
    #
    @46
    @44
    @49
    @20
    @43
    @0
    w3a
    @42
    @24
    wss
    #
    cC
    @42
    cin
    #
    c0h
    wceq
    #
    wa
    @46
    @49
    @20
    @43
    @0
    @1
    @20
    @0
    @40
    @21
    ad2antlr
    @2
    @40
    @43
    @48
    imp
    @0
    @1
    @40
    simpll
    3jca
    @49
    @50
    @52
    @2
    @50
    @40
    @2
    @41
    @42
    @24
    cA
    @41
    inss2
    @0
    @29
    @20
    @41
    @24
    wceq
    @1
    @30
    @21
    cB
    cC
    chjcom
    syl2an
    syl5sseq
    adantr
    @2
    @39
    @52
    @7
    @2
    @38
    @52
    @37
    @2
    @38
    @52
    @2
    @38
    cA
    cC
    cin
    #
    c0h
    wceq
    #
    @52
    @1
    @38
    @54
    wb
    #
    @0
    @34
    @1
    @55
    atcvat3.1
    cA
    cC
    atnssm0
    mpan
    adantl
    @54
    @51
    c0h
    wss
    #
    @2
    @52
    @54
    @51
    @53
    wss
    @56
    @51
    cC
    cA
    cin
    #
    @53
    @44
    @51
    @57
    wss
    cA
    @41
    inss1
    #
    @42
    cA
    cC
    sslin
    ax-mp
    cC
    cA
    incom
    sseqtri
    @53
    c0h
    @51
    sseq2
    mpbii
    @2
    @51
    cch
    wcel
    #
    @56
    @52
    wb
    @0
    @29
    @20
    @59
    @1
    @30
    @21
    @31
    @20
    @42
    cch
    wcel
    #
    @59
    @29
    @20
    simpr
    @31
    @34
    @41
    cch
    wcel
    @60
    atcvat3.1
    cB
    cC
    chjcl
    cA
    @41
    chincl
    sylancr
    cC
    @42
    chincl
    syl2anc
    syl2an
    @51
    chle0
    syl
    syl5ib
    sylbid
    imp
    adantrl
    adantrr
    jca
    cC
    @42
    cB
    atexch
    sylc
    @58
    jctil
    ex
    jcad
    @13
    @47
    vx
    @42
    cat
    @9
    @42
    wceq
    #
    @10
    @44
    @12
    @46
    @9
    @42
    cA
    sseq1
    @61
    @11
    @45
    cB
    @9
    @42
    cC
    chj
    oveq2
    sseq2d
    anbi12d
    rspcev
    syl6
    expd
    syl5bi
    syl7
    ecase3d
end
