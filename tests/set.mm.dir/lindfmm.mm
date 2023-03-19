include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "wf1.mm"
include "wf.mm"
include "w3a.mm"
include "cvv.mm"
include "clindf.mm"
include "wbr.mm"
include "ccom.mm"
include "rellindf.mm"
include "brrelexi.mm"
include "simp3.mm"
include "dmfex.mm"
include "syl2anr.mm"
include "ex.mm"
include "f1f.mm"
include "fco.mm"
include "sylan.mm"
include "3adant1.mm"
include "wb.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cvsca.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "clspn.mm"
include "wn.mm"
include "csca.mm"
include "cbs.mm"
include "c0g.mm"
include "wral.mm"
include "eldifi.mm"
include "wss.mm"
include "simpllr.mm"
include "clmod.mm"
include "lmhmlmod1.mm"
include "ad3antrrr.mm"
include "simprr.mm"
include "simprl.mm"
include "simpl.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "eqid.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "adantr.mm"
include "syl5ss.mm"
include "ad2antlr.mm"
include "lspssv.mm"
include "syl2anc.mm"
include "f1elima.mm"
include "wceq.mm"
include "simplll.mm"
include "lmhmlin.mm"
include "wfn.mm"
include "ffn.mm"
include "ad2antrl.mm"
include "fvco2.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "lmhmlsp.mm"
include "imaco.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "eleq12d.mm"
include "bitr3d.mm"
include "notbid.mm"
include "anassrs.mm"
include "sylan2.mm"
include "ralbidva.mm"
include "lmhmsca.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "raleqdv.mm"
include "bitr4d.mm"
include "ad2antrr.mm"
include "islindf2.mm"
include "lmhmlmod2.mm"
include "ad2ant2lr.mm"
include "3bitr4d.mm"
include "exp32.mm"
include "3impia.mm"
include "pm5.21ndd.mm"

theorem lindfmm
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cI: class I
  let vk: setvar k
  let vx: setvar x
  assume lindfmm.b: |- B = ( Base ` S )
  assume lindfmm.c: |- C = ( Base ` T )


  assert |- ( ( G e. ( S LMHom T ) /\ G : B -1-1-> C /\ F : I --> B ) -> ( F LIndF S <-> ( G o. F ) LIndF T ) )

  proof
    cG
    cS
    cT
    clmhm
    co
    wcel
    #
    cB
    cC
    cG
    wf1
    #
    cI
    cB
    cF
    wf
    #
    w3a
    #
    cI
    cvv
    wcel
    #
    cF
    cS
    clindf
    wbr
    #
    cG
    cF
    ccom
    #
    cT
    clindf
    wbr
    #
    @3
    @5
    @4
    @5
    cF
    cvv
    wcel
    @2
    @4
    @3
    cF
    cS
    clindf
    rellindf
    brrelexi
    @0
    @1
    @2
    simp3
    cI
    cB
    cvv
    cF
    dmfex
    syl2anr
    ex
    @3
    @7
    @4
    @7
    @6
    cvv
    wcel
    cI
    cC
    @6
    wf
    #
    @4
    @3
    @6
    cT
    clindf
    rellindf
    brrelexi
    @1
    @2
    @8
    @0
    @1
    cB
    cC
    cG
    wf
    @2
    @8
    cB
    cC
    cG
    f1f
    cI
    cB
    cC
    cG
    cF
    fco
    sylan
    #
    3adant1
    cI
    cC
    cvv
    @6
    dmfex
    syl2anr
    ex
    @0
    @1
    @2
    @4
    @5
    @7
    wb
    #
    wi
    @0
    @1
    wa
    #
    @2
    @4
    @10
    @11
    @2
    @4
    wa
    #
    wa
    #
    vk
    cv
    #
    vx
    cv
    #
    cF
    cfv
    #
    cS
    cvsca
    cfv
    #
    co
    #
    cF
    cI
    @15
    csn
    cdif
    #
    cima
    #
    cS
    clspn
    cfv
    #
    cfv
    #
    wcel
    #
    wn
    #
    vk
    cS
    csca
    cfv
    #
    cbs
    cfv
    #
    @25
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    #
    vx
    cI
    wral
    #
    @14
    @15
    @6
    cfv
    #
    cT
    cvsca
    cfv
    #
    co
    #
    @6
    @19
    cima
    #
    cT
    clspn
    cfv
    #
    cfv
    #
    wcel
    #
    wn
    #
    vk
    cT
    csca
    cfv
    #
    cbs
    cfv
    #
    @40
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    #
    vx
    cI
    wral
    #
    @5
    @7
    @13
    @30
    @45
    vx
    cI
    @13
    @15
    cI
    wcel
    #
    wa
    #
    @30
    @39
    vk
    @29
    wral
    @45
    @48
    @24
    @39
    vk
    @29
    @14
    @29
    wcel
    @48
    @14
    @26
    wcel
    #
    @24
    @39
    wb
    #
    @14
    @26
    @28
    eldifi
    @13
    @47
    @49
    @50
    @13
    @47
    @49
    wa
    #
    wa
    #
    @23
    @38
    @52
    @18
    cG
    cfv
    #
    cG
    @22
    cima
    #
    wcel
    #
    @23
    @38
    @52
    @1
    @18
    cB
    wcel
    #
    @22
    cB
    wss
    #
    @55
    @23
    wb
    @0
    @1
    @12
    @51
    simpllr
    @52
    cS
    clmod
    wcel
    #
    @49
    @16
    cB
    wcel
    #
    @56
    @0
    @58
    @1
    @12
    @51
    cS
    cT
    cG
    lmhmlmod1
    #
    ad3antrrr
    #
    @13
    @47
    @49
    simprr
    #
    @13
    @2
    @47
    @59
    @51
    @11
    @2
    @4
    simprl
    #
    @47
    @49
    simpl
    #
    cI
    cB
    @15
    cF
    ffvelrn
    syl2an
    #
    @14
    @17
    @25
    @26
    cB
    cS
    @16
    lindfmm.b
    @25
    eqid
    #
    @17
    eqid
    #
    @26
    eqid
    #
    lmodvscl
    syl3anc
    @52
    @58
    @20
    cB
    wss
    #
    @57
    @61
    @12
    @69
    @11
    @51
    @12
    @20
    cF
    crn
    #
    cB
    cF
    @19
    imassrn
    @2
    @70
    cB
    wss
    @4
    cI
    cB
    cF
    frn
    adantr
    syl5ss
    ad2antlr
    #
    @20
    @21
    cB
    cS
    lindfmm.b
    @21
    eqid
    #
    lspssv
    syl2anc
    cB
    cC
    cG
    @18
    @22
    f1elima
    syl3anc
    @52
    @53
    @34
    @54
    @37
    @52
    @53
    @14
    @16
    cG
    cfv
    #
    @33
    co
    #
    @34
    @52
    @0
    @49
    @59
    @53
    @74
    wceq
    @0
    @1
    @12
    @51
    simplll
    #
    @62
    @65
    @26
    cS
    cT
    @17
    @33
    cB
    cG
    @25
    @14
    @16
    @66
    @68
    lindfmm.b
    @67
    @33
    eqid
    #
    lmhmlin
    syl3anc
    @52
    @32
    @73
    @14
    @33
    @13
    cF
    cI
    wfn
    #
    @47
    @32
    @73
    wceq
    @51
    @2
    @77
    @11
    @4
    cI
    cB
    cF
    ffn
    ad2antrl
    @64
    cI
    cG
    cF
    @15
    fvco2
    syl2an
    oveq2d
    eqtr4d
    @52
    @54
    cG
    @20
    cima
    #
    @36
    cfv
    #
    @37
    @52
    @0
    @69
    @54
    @79
    wceq
    @75
    @71
    cS
    cT
    @20
    cG
    @21
    @36
    cB
    lindfmm.b
    @72
    @36
    eqid
    #
    lmhmlsp
    syl2anc
    @35
    @78
    @36
    cG
    cF
    @19
    imaco
    fveq2i
    syl6eqr
    eleq12d
    bitr3d
    notbid
    anassrs
    sylan2
    ralbidva
    @48
    @39
    vk
    @44
    @29
    @0
    @44
    @29
    wceq
    @1
    @12
    @47
    @0
    @41
    @26
    @43
    @28
    @0
    @40
    @25
    cbs
    cS
    cT
    cG
    @25
    @40
    @66
    @40
    eqid
    #
    lmhmsca
    #
    fveq2d
    @0
    @42
    @27
    @0
    @40
    @25
    c0g
    @82
    fveq2d
    sneqd
    difeq12d
    ad3antrrr
    raleqdv
    bitr4d
    ralbidva
    @13
    @58
    @4
    @2
    @5
    @31
    wb
    @0
    @58
    @1
    @12
    @60
    ad2antrr
    @11
    @2
    @4
    simprr
    #
    @63
    vx
    cB
    @25
    @17
    vk
    cF
    cI
    @21
    @26
    cS
    cvv
    clmod
    @27
    lindfmm.b
    @67
    @72
    @66
    @68
    @27
    eqid
    islindf2
    syl3anc
    @13
    cT
    clmod
    wcel
    #
    @4
    @8
    @7
    @46
    wb
    @0
    @84
    @1
    @12
    cS
    cT
    cG
    lmhmlmod2
    ad2antrr
    @83
    @1
    @2
    @8
    @0
    @4
    @9
    ad2ant2lr
    vx
    cC
    @40
    @33
    vk
    @6
    cI
    @36
    @41
    cT
    cvv
    clmod
    @42
    lindfmm.c
    @76
    @80
    @81
    @41
    eqid
    @42
    eqid
    islindf2
    syl3anc
    3bitr4d
    exp32
    3impia
    pm5.21ndd
end
