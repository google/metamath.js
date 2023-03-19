include "c0.mm"
include "wceq.mm"
include "cprod.mm"
include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wa.mm"
include "wss.mm"
include "sseq2.mm"
include "ss0.mm"
include "syl6bi.mm"
include "prodeq1.mm"
include "eqcomd.mm"
include "sylan9eq.mm"
include "expcom.mm"
include "syld.mm"
include "syl5com.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "simprr.mm"
include "f1of.mm"
include "syl.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "cc.mm"
include "wfn.mm"
include "wb.mm"
include "f1ofn.mm"
include "elpreima.mm"
include "ffvelrnda.mm"
include "ex.mm"
include "adantrd.mm"
include "sylbid.mm"
include "imp.mm"
include "wi.mm"
include "adantr.mm"
include "wn.mm"
include "cdif.mm"
include "eldif.mm"
include "ax-1cn.mm"
include "syl6eqel.mm"
include "sylan2br.mm"
include "expr.mm"
include "pm2.61d.mm"
include "adantlr.mm"
include "eqid.mm"
include "fmptd.mm"
include "syldan.mm"
include "cuz.mm"
include "simprl.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "ssid.mm"
include "a1i.mm"
include "fprodntriv.mm"
include "eldifi.mm"
include "sylan2.mm"
include "eldifn.mm"
include "adantl.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "mtbid.mm"
include "eldifd.mm"
include "cres.mm"
include "difss.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "fveq1i.mm"
include "fvres.mm"
include "syl5eqr.mm"
include "csn.mm"
include "1ex.mm"
include "elsn2.mm"
include "sylibr.mm"
include "ad2antrr.mm"
include "ffvelrnd.mm"
include "elsni.mm"
include "eqtr3d.mm"
include "fzssuz.mm"
include "prodss.mm"
include "resmptd.mm"
include "fveq1d.mm"
include "sylan9req.mm"
include "prodeq2dv.mm"
include "fveq2.mm"
include "fzfid.mm"
include "fisuppfi.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1ores.mm"
include "syl2anc.mm"
include "wfo.mm"
include "f1ofo.mm"
include "foimacnv.mm"
include "f1oeq3.mm"
include "mpbid.mm"
include "sselda.mm"
include "fprodf1o.mm"
include "eqtrd.mm"
include "eqidd.mm"
include "3eqtr4d.mm"
include "prodfc.mm"
include "3eqtr3g.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem fprodss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
  assume fprodss.1: |- ( ph -> A C_ B )
  assume fprodss.2: |- ( ( ph /\ k e. A ) -> C e. CC )
  assume fprodss.3: |- ( ( ph /\ k e. ( B \ A ) ) -> C = 1 )
  assume fprodss.4: |- ( ph -> B e. Fin )

  disjoint A k
  disjoint B k
  disjoint k ph
  disjoint A f
  disjoint A m
  disjoint A n
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint C f
  disjoint C m
  disjoint C n
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f ph
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint m ph
  disjoint n ph
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint f y
  disjoint k y
  disjoint m y
  disjoint n y
  disjoint ph y
  assert |- ( ph -> prod_ k e. A C = prod_ k e. B C )

  proof
    wph
    cB
    c0
    wceq
    #
    cA
    cC
    vk
    cprod
    #
    cB
    cC
    vk
    cprod
    #
    wceq
    #
    cB
    chash
    cfv
    #
    cn
    wcel
    #
    c1
    @4
    cfz
    co
    #
    cB
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    wa
    #
    wph
    cA
    cB
    wss
    #
    @0
    @3
    fprodss.1
    @0
    @11
    cA
    c0
    wceq
    #
    @3
    @0
    @11
    cA
    c0
    wss
    @12
    cB
    c0
    cA
    sseq2
    cA
    ss0
    syl6bi
    @12
    @0
    @3
    @12
    @0
    @1
    c0
    cC
    vk
    cprod
    #
    @2
    cA
    c0
    cC
    vk
    prodeq1
    @0
    @2
    @13
    cB
    c0
    cC
    vk
    prodeq1
    eqcomd
    sylan9eq
    expcom
    syld
    syl5com
    wph
    @5
    @9
    @3
    wph
    @5
    wa
    @8
    @3
    vf
    wph
    @5
    @8
    @3
    wph
    @5
    @8
    wa
    #
    wa
    #
    cA
    vm
    cv
    #
    vk
    cA
    cC
    cmpt
    #
    cfv
    #
    vm
    cprod
    #
    cB
    @16
    vk
    cB
    cC
    cmpt
    #
    cfv
    #
    vm
    cprod
    #
    @1
    @2
    @15
    @7
    ccnv
    cA
    cima
    #
    vn
    cv
    #
    @7
    cfv
    #
    @20
    cfv
    #
    vn
    cprod
    #
    @6
    @26
    vn
    cprod
    @19
    @22
    @15
    vy
    @23
    @6
    @26
    vn
    vm
    c1
    @15
    @7
    cdm
    #
    @23
    @6
    @7
    cA
    cnvimass
    @15
    @6
    cB
    @7
    wf
    #
    @28
    @6
    wceq
    @15
    @8
    @29
    wph
    @5
    @8
    simprr
    #
    @6
    cB
    @7
    f1of
    syl
    #
    @6
    cB
    @7
    fdm
    syl
    syl5sseq
    #
    @15
    @24
    @23
    wcel
    #
    @25
    cB
    wcel
    #
    @26
    cc
    wcel
    @15
    @33
    @34
    @15
    @33
    @24
    @6
    wcel
    #
    @25
    cA
    wcel
    #
    wa
    #
    @34
    @15
    @7
    @6
    wfn
    #
    @33
    @37
    wb
    #
    @15
    @8
    @38
    @30
    @6
    cB
    @7
    f1ofn
    syl
    @6
    @24
    cA
    @7
    elpreima
    syl
    #
    @15
    @35
    @34
    @36
    @15
    @35
    @34
    @15
    @6
    cB
    @24
    @7
    @31
    ffvelrnda
    #
    ex
    adantrd
    sylbid
    imp
    @15
    cB
    cc
    @25
    @20
    @15
    vk
    cB
    cC
    cc
    @20
    wph
    vk
    cv
    #
    cB
    wcel
    #
    cC
    cc
    wcel
    #
    @14
    wph
    @43
    wa
    @42
    cA
    wcel
    #
    @44
    wph
    @45
    @44
    wi
    @43
    wph
    @45
    @44
    fprodss.2
    ex
    adantr
    wph
    @43
    @45
    wn
    #
    @44
    @43
    @46
    wa
    wph
    @42
    cB
    cA
    cdif
    #
    wcel
    #
    @44
    @42
    cB
    cA
    eldif
    wph
    @48
    wa
    #
    cC
    c1
    cc
    fprodss.3
    ax-1cn
    syl6eqel
    sylan2br
    expr
    pm2.61d
    adantlr
    @20
    eqid
    fmptd
    #
    ffvelrnda
    syldan
    @15
    vy
    @6
    @26
    vn
    vm
    c1
    @4
    c1
    cuz
    cfv
    #
    @51
    eqid
    @15
    @4
    cn
    @51
    wph
    @5
    @8
    simprl
    nnuz
    syl6eleq
    @6
    @6
    wss
    @15
    @6
    ssid
    a1i
    fprodntriv
    @15
    @24
    @6
    @23
    cdif
    wcel
    #
    wa
    #
    @25
    vk
    @47
    cC
    cmpt
    #
    cfv
    #
    @26
    c1
    @53
    @25
    @47
    wcel
    #
    @55
    @26
    wceq
    @53
    @25
    cB
    cA
    @52
    @15
    @35
    @34
    @24
    @6
    @23
    eldifi
    #
    @41
    sylan2
    @53
    @33
    @36
    @52
    @33
    wn
    @15
    @24
    @6
    @23
    eldifn
    adantl
    @53
    @33
    @37
    @36
    @15
    @39
    @52
    @40
    adantr
    @53
    @35
    @36
    @52
    @35
    @15
    @57
    adantl
    biantrurd
    bitr4d
    mtbid
    eldifd
    #
    @56
    @55
    @25
    @20
    @47
    cres
    #
    cfv
    @26
    @25
    @59
    @54
    @47
    cB
    wss
    @59
    @54
    wceq
    cB
    cA
    difss
    vk
    cB
    @47
    cC
    resmpt
    ax-mp
    fveq1i
    @25
    @47
    @20
    fvres
    syl5eqr
    syl
    @53
    @55
    c1
    csn
    #
    wcel
    @55
    c1
    wceq
    @53
    @47
    @60
    @25
    @54
    wph
    @47
    @60
    @54
    wf
    @14
    @52
    wph
    vk
    @47
    cC
    @60
    @54
    @49
    cC
    c1
    wceq
    cC
    @60
    wcel
    fprodss.3
    cC
    c1
    1ex
    elsn2
    sylibr
    @54
    eqid
    fmptd
    ad2antrr
    @58
    ffvelrnd
    @55
    c1
    elsni
    syl
    eqtr3d
    @6
    @51
    wss
    @15
    c1
    @4
    fzssuz
    a1i
    prodss
    @15
    @19
    cA
    @21
    vm
    cprod
    @27
    @15
    cA
    @18
    @21
    vm
    @15
    @16
    cA
    wcel
    #
    @18
    @16
    @20
    cA
    cres
    #
    cfv
    @21
    @15
    @16
    @62
    @17
    @15
    vk
    cB
    cA
    cC
    wph
    @11
    @14
    fprodss.1
    adantr
    #
    resmptd
    fveq1d
    @16
    cA
    @20
    fvres
    sylan9req
    prodeq2dv
    @15
    cA
    @21
    @23
    @26
    vm
    vn
    @7
    @23
    cres
    #
    @25
    @16
    @25
    @20
    fveq2
    #
    @15
    @6
    cB
    cA
    @7
    @15
    c1
    @4
    fzfid
    #
    @31
    fisuppfi
    @15
    @23
    @7
    @23
    cima
    #
    @64
    wf1o
    #
    @23
    cA
    @64
    wf1o
    #
    @15
    @6
    cB
    @7
    wf1
    #
    @23
    @6
    wss
    @68
    @15
    @8
    @70
    @30
    @6
    cB
    @7
    f1of1
    syl
    @32
    @6
    cB
    @23
    @7
    f1ores
    syl2anc
    @15
    @67
    cA
    wceq
    #
    @68
    @69
    wb
    @15
    @6
    cB
    @7
    wfo
    #
    @11
    @71
    @15
    @8
    @72
    @30
    @6
    cB
    @7
    f1ofo
    syl
    @63
    @6
    cB
    cA
    @7
    foimacnv
    syl2anc
    @67
    cA
    @23
    @64
    f1oeq3
    syl
    mpbid
    @33
    @24
    @64
    cfv
    @25
    wceq
    @15
    @24
    @23
    @7
    fvres
    adantl
    @15
    @61
    @16
    cB
    wcel
    @21
    cc
    wcel
    @15
    cA
    cB
    @16
    @63
    sselda
    @15
    cB
    cc
    @16
    @20
    @50
    ffvelrnda
    #
    syldan
    fprodf1o
    eqtrd
    @15
    cB
    @21
    @6
    @26
    vm
    vn
    @7
    @25
    @65
    @66
    @30
    @15
    @35
    wa
    @25
    eqidd
    @73
    fprodf1o
    3eqtr4d
    cA
    cC
    vm
    vk
    prodfc
    cB
    cC
    vm
    vk
    prodfc
    3eqtr3g
    expr
    exlimdv
    expimpd
    wph
    cB
    cfn
    wcel
    @0
    @10
    wo
    fprodss.4
    cB
    vf
    fz1f1o
    syl
    mpjaod
end
