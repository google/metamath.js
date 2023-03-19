include "cixp.mm"
include "wcel.mm"
include "cdif.mm"
include "wss.mm"
include "w3a.mm"
include "cun.mm"
include "cvv.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "unexg.mm"
include "3adant3.mm"
include "wi.mm"
include "ixpfn.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "3simpa.mm"
include "ancomd.mm"
include "disjdif.mm"
include "fnun.mm"
include "sylancl.mm"
include "undif.mm"
include "biimpi.mm"
include "eqcomd.mm"
include "3ad2ant3.mm"
include "fneq2d.mm"
include "mpbird.mm"
include "3exp.mm"
include "syl2imc.mm"
include "3imp.mm"
include "elixp2.mm"
include "simp3bi.mm"
include "cdm.mm"
include "wn.mm"
include "fndm.mm"
include "elndif.mm"
include "wb.mm"
include "eleq2.mm"
include "notbid.mm"
include "eqcoms.mm"
include "ndmfv.mm"
include "syl6bi.mm"
include "syl2im.mm"
include "ralrimiv.mm"
include "uneq2.mm"
include "un0.mm"
include "eqtr.mm"
include "eleq1.mm"
include "biimpd.mm"
include "syl.mm"
include "com12.mm"
include "ral2imi.mm"
include "impcom.mm"
include "eldifn.mm"
include "uneq1.mm"
include "uncom.mm"
include "imp.mm"
include "ralunb.mm"
include "sylanbrc.mm"
include "ex.mm"
include "raleq.mm"
include "imbi2d.mm"
include "syl5ibr.mm"
include "sylbi.mm"
include "3imp231.mm"
include "wfun.mm"
include "df-fn.mm"
include "simpl.mm"
include "anim12i.mm"
include "ineq12.mm"
include "syl6eq.mm"
include "ad2ant2l.mm"
include "fvun.mm"
include "syl2anc.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "syl3anbrc.mm"

theorem undifixp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint G x
  assert |- ( ( F e. X_ x e. B C /\ G e. X_ x e. ( A \ B ) C /\ B C_ A ) -> ( F u. G ) e. X_ x e. A C )

  proof
    cF
    vx
    cB
    cC
    cixp
    #
    wcel
    #
    cG
    vx
    cA
    cB
    cdif
    #
    cC
    cixp
    #
    wcel
    #
    cB
    cA
    wss
    #
    w3a
    #
    cF
    cG
    cun
    #
    cvv
    wcel
    #
    @7
    cA
    wfn
    #
    vx
    cv
    #
    @7
    cfv
    #
    cC
    wcel
    #
    vx
    cA
    wral
    #
    @7
    vx
    cA
    cC
    cixp
    wcel
    @1
    @4
    @8
    @5
    cF
    cG
    @0
    @3
    unexg
    3adant3
    @1
    @4
    @5
    @9
    @4
    cG
    @2
    wfn
    #
    @1
    cF
    cB
    wfn
    #
    @5
    @9
    wi
    vx
    @2
    cC
    cG
    ixpfn
    #
    vx
    cB
    cC
    cF
    ixpfn
    #
    @14
    @15
    @5
    @9
    @14
    @15
    @5
    w3a
    #
    @9
    @7
    cB
    @2
    cun
    #
    wfn
    #
    @18
    @15
    @14
    wa
    cB
    @2
    cin
    #
    c0
    wceq
    @20
    @18
    @14
    @15
    @14
    @15
    @5
    3simpa
    ancomd
    cB
    cA
    disjdif
    #
    cB
    @2
    cF
    cG
    fnun
    sylancl
    @18
    cA
    @19
    @7
    @5
    @14
    cA
    @19
    wceq
    #
    @15
    @5
    @19
    cA
    @5
    @19
    cA
    wceq
    #
    cB
    cA
    undif
    #
    biimpi
    eqcomd
    3ad2ant3
    fneq2d
    mpbird
    3exp
    syl2imc
    3imp
    @6
    @13
    @10
    cF
    cfv
    #
    @10
    cG
    cfv
    #
    cun
    #
    cC
    wcel
    #
    vx
    cA
    wral
    #
    @5
    @1
    @4
    @30
    @5
    @24
    @1
    @4
    @30
    wi
    #
    wi
    #
    @25
    @32
    cA
    @19
    @1
    @31
    @23
    @4
    @29
    vx
    @19
    wral
    #
    wi
    @1
    @4
    @33
    @1
    @4
    wa
    @29
    vx
    cB
    wral
    #
    @29
    vx
    @2
    wral
    #
    @33
    @4
    @1
    @34
    @4
    @14
    @1
    @34
    wi
    @16
    @1
    @26
    cC
    wcel
    #
    vx
    cB
    wral
    #
    @14
    @27
    c0
    wceq
    #
    vx
    cB
    wral
    @34
    @1
    cF
    cvv
    wcel
    @15
    @37
    vx
    cB
    cC
    cF
    elixp2
    simp3bi
    @14
    @38
    vx
    cB
    @14
    cG
    cdm
    #
    @2
    wceq
    #
    @10
    cB
    wcel
    #
    @10
    @2
    wcel
    #
    wn
    #
    @38
    @2
    cG
    fndm
    @10
    cB
    cA
    elndif
    @40
    @43
    @10
    @39
    wcel
    #
    wn
    #
    @38
    @43
    @45
    wb
    @2
    @39
    @2
    @39
    wceq
    @42
    @44
    @2
    @39
    @10
    eleq2
    notbid
    eqcoms
    @10
    cG
    ndmfv
    syl6bi
    syl2im
    ralrimiv
    @36
    @38
    @29
    vx
    cB
    @38
    @36
    @29
    @38
    @28
    @26
    c0
    cun
    #
    wceq
    #
    @46
    @26
    wceq
    #
    @36
    @29
    wi
    #
    @27
    c0
    @26
    uneq2
    @26
    un0
    @47
    @48
    wa
    @28
    @26
    wceq
    @49
    @28
    @46
    @26
    eqtr
    @49
    @26
    @28
    @26
    @28
    wceq
    @36
    @29
    @26
    @28
    cC
    eleq1
    biimpd
    eqcoms
    syl
    sylancl
    com12
    ral2imi
    syl2imc
    syl
    impcom
    @1
    @4
    @35
    @1
    @15
    @4
    @35
    wi
    @17
    @4
    @27
    cC
    wcel
    #
    vx
    @2
    wral
    #
    @15
    @26
    c0
    wceq
    #
    vx
    @2
    wral
    @35
    @4
    cG
    cvv
    wcel
    @14
    @51
    vx
    @2
    cC
    cG
    elixp2
    simp3bi
    @15
    @52
    vx
    @2
    @15
    cF
    cdm
    #
    cB
    wceq
    #
    @42
    @41
    wn
    #
    @52
    cB
    cF
    fndm
    @10
    cA
    cB
    eldifn
    @55
    @52
    wi
    cB
    @53
    cB
    @53
    wceq
    #
    @55
    @10
    @53
    wcel
    #
    wn
    @52
    @56
    @41
    @57
    cB
    @53
    @10
    eleq2
    notbid
    @10
    cF
    ndmfv
    syl6bi
    eqcoms
    syl2im
    ralrimiv
    @50
    @52
    @29
    vx
    @2
    @52
    @50
    @29
    @52
    @28
    c0
    @27
    cun
    #
    wceq
    #
    @58
    @27
    c0
    cun
    #
    wceq
    #
    @50
    @29
    wi
    #
    @26
    c0
    @27
    uneq1
    c0
    @27
    uncom
    @59
    @61
    wa
    @28
    @60
    wceq
    #
    @60
    @27
    wceq
    #
    @62
    @28
    @58
    @60
    eqtr
    @27
    un0
    @63
    @64
    wa
    @28
    @27
    wceq
    @62
    @28
    @60
    @27
    eqtr
    @62
    @27
    @28
    @27
    @28
    wceq
    @50
    @29
    @27
    @28
    cC
    eleq1
    biimpd
    eqcoms
    syl
    sylancl
    sylancl
    com12
    ral2imi
    syl2imc
    syl
    imp
    @29
    vx
    cB
    @2
    ralunb
    sylanbrc
    ex
    @23
    @30
    @33
    @4
    @29
    vx
    cA
    @19
    raleq
    imbi2d
    syl5ibr
    eqcoms
    sylbi
    3imp231
    @1
    @4
    @5
    @13
    @30
    wb
    #
    @4
    @14
    @1
    @15
    @5
    @65
    wi
    #
    @16
    @17
    @14
    cG
    wfun
    #
    @40
    wa
    #
    @15
    @66
    wi
    cG
    @2
    df-fn
    @15
    @68
    @66
    @15
    cF
    wfun
    #
    @54
    wa
    #
    @68
    @66
    wi
    cF
    cB
    df-fn
    @70
    @68
    @5
    @65
    @70
    @68
    @5
    w3a
    #
    @12
    @29
    vx
    cA
    @71
    @11
    @28
    cC
    @71
    @69
    @67
    wa
    #
    @53
    @39
    cin
    #
    c0
    wceq
    #
    @11
    @28
    wceq
    @70
    @68
    @72
    @5
    @70
    @69
    @68
    @67
    @69
    @54
    simpl
    @67
    @40
    simpl
    anim12i
    3adant3
    @70
    @68
    @74
    @5
    @54
    @40
    @74
    @69
    @67
    @54
    @40
    wa
    @73
    @21
    c0
    @53
    cB
    @39
    @2
    ineq12
    @22
    syl6eq
    ad2ant2l
    3adant3
    @10
    cF
    cG
    fvun
    syl2anc
    eleq1d
    ralbidv
    3exp
    sylbi
    com12
    sylbi
    syl2imc
    3imp
    mpbird
    vx
    cA
    cC
    @7
    elixp2
    syl3anbrc
end
