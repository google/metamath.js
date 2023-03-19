include "c0.mm"
include "wceq.mm"
include "csu.mm"
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
include "cc0.mm"
include "wss.mm"
include "adantr.mm"
include "cc.mm"
include "adantlr.mm"
include "cdif.mm"
include "cuz.mm"
include "simpr.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "sumss.mm"
include "ex.mm"
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
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "ffvelrnda.mm"
include "adantrd.mm"
include "sylbid.mm"
include "imp.mm"
include "wi.mm"
include "wn.mm"
include "eldif.mm"
include "0cn.mm"
include "syl6eqel.mm"
include "sylan2br.mm"
include "expr.mm"
include "pm2.61d.mm"
include "eqid.mm"
include "fmptd.mm"
include "syldan.mm"
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
include "c0ex.mm"
include "elsn2.mm"
include "sylibr.mm"
include "ad2antrr.mm"
include "ffvelrnd.mm"
include "elsni.mm"
include "eqtr3d.mm"
include "fzssuz.mm"
include "a1i.mm"
include "resmptd.mm"
include "fveq1d.mm"
include "sumeq2dv.mm"
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
include "fsumf1o.mm"
include "eqtrd.mm"
include "eqidd.mm"
include "3eqtr4d.mm"
include "sumfc.mm"
include "3eqtr3g.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem fsumss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let cM: class M
  assume sumss.1: |- ( ph -> A C_ B )
  assume sumss.2: |- ( ( ph /\ k e. A ) -> C e. CC )
  assume sumss.3: |- ( ( ph /\ k e. ( B \ A ) ) -> C = 0 )
  assume fsumss.4: |- ( ph -> B e. Fin )

  disjoint A k
  disjoint B k
  disjoint k ph
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint A f
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint A m
  disjoint A n
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint C f
  disjoint C m
  disjoint C n
  disjoint f ph
  disjoint m ph
  disjoint n ph
  disjoint M k
  disjoint M m
  assert |- ( ph -> sum_ k e. A C = sum_ k e. B C )

  proof
    wph
    cB
    c0
    wceq
    #
    cA
    cC
    vk
    csu
    #
    cB
    cC
    vk
    csu
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
    @0
    @3
    wph
    @0
    wa
    #
    cA
    cB
    cC
    vk
    cc0
    wph
    cA
    cB
    wss
    #
    @0
    sumss.1
    adantr
    wph
    vk
    cv
    #
    cA
    wcel
    #
    cC
    cc
    wcel
    #
    @0
    sumss.2
    adantlr
    wph
    @13
    cB
    cA
    cdif
    #
    wcel
    #
    cC
    cc0
    wceq
    #
    @0
    sumss.3
    adantlr
    @11
    cB
    c0
    cc0
    cuz
    cfv
    #
    wph
    @0
    simpr
    @19
    0ss
    syl6eqss
    sumss
    ex
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
    csu
    #
    cB
    @22
    vk
    cB
    cC
    cmpt
    #
    cfv
    #
    vm
    csu
    #
    @1
    @2
    @21
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
    @26
    cfv
    #
    vn
    csu
    #
    @6
    @32
    vn
    csu
    @25
    @28
    @21
    @29
    @6
    @32
    vn
    c1
    @21
    @7
    cdm
    #
    @29
    @6
    @7
    cA
    cnvimass
    @21
    @6
    cB
    @7
    wf
    #
    @34
    @6
    wceq
    @21
    @8
    @35
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
    @21
    @30
    @29
    wcel
    #
    @31
    cB
    wcel
    #
    @32
    cc
    wcel
    @21
    @39
    @40
    @21
    @39
    @30
    @6
    wcel
    #
    @31
    cA
    wcel
    #
    wa
    #
    @40
    @21
    @7
    @6
    wfn
    #
    @39
    @43
    wb
    #
    @21
    @35
    @44
    @37
    @6
    cB
    @7
    ffn
    syl
    @6
    @30
    cA
    @7
    elpreima
    syl
    #
    @21
    @41
    @40
    @42
    @21
    @41
    @40
    @21
    @6
    cB
    @30
    @7
    @37
    ffvelrnda
    #
    ex
    adantrd
    sylbid
    imp
    @21
    cB
    cc
    @31
    @26
    wph
    cB
    cc
    @26
    wf
    @20
    wph
    vk
    cB
    cC
    cc
    @26
    wph
    @13
    cB
    wcel
    #
    wa
    @14
    @15
    wph
    @14
    @15
    wi
    @48
    wph
    @14
    @15
    sumss.2
    ex
    adantr
    wph
    @48
    @14
    wn
    #
    @15
    @48
    @49
    wa
    wph
    @17
    @15
    @13
    cB
    cA
    eldif
    wph
    @17
    wa
    #
    cC
    cc0
    cc
    sumss.3
    0cn
    syl6eqel
    sylan2br
    expr
    pm2.61d
    @26
    eqid
    fmptd
    adantr
    #
    ffvelrnda
    syldan
    @21
    @30
    @6
    @29
    cdif
    wcel
    #
    wa
    #
    @31
    vk
    @16
    cC
    cmpt
    #
    cfv
    #
    @32
    cc0
    @53
    @31
    @16
    wcel
    #
    @55
    @32
    wceq
    @53
    @31
    cB
    cA
    @52
    @21
    @41
    @40
    @30
    @6
    @29
    eldifi
    #
    @47
    sylan2
    @53
    @39
    @42
    @52
    @39
    wn
    @21
    @30
    @6
    @29
    eldifn
    adantl
    @53
    @39
    @43
    @42
    @21
    @45
    @52
    @46
    adantr
    @53
    @41
    @42
    @52
    @41
    @21
    @57
    adantl
    biantrurd
    bitr4d
    mtbid
    eldifd
    #
    @56
    @55
    @31
    @26
    @16
    cres
    #
    cfv
    @32
    @31
    @59
    @54
    @16
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
    @16
    cC
    resmpt
    ax-mp
    fveq1i
    @31
    @16
    @26
    fvres
    syl5eqr
    syl
    @53
    @55
    cc0
    csn
    #
    wcel
    @55
    cc0
    wceq
    @53
    @16
    @60
    @31
    @54
    wph
    @16
    @60
    @54
    wf
    @20
    @52
    wph
    vk
    @16
    cC
    @60
    @54
    @50
    @18
    cC
    @60
    wcel
    sumss.3
    cC
    cc0
    c0ex
    elsn2
    sylibr
    @54
    eqid
    fmptd
    ad2antrr
    @58
    ffvelrnd
    @55
    cc0
    elsni
    syl
    eqtr3d
    @6
    c1
    cuz
    cfv
    wss
    @21
    c1
    @4
    fzssuz
    a1i
    sumss
    @21
    @25
    cA
    @27
    vm
    csu
    @33
    @21
    cA
    @24
    @27
    vm
    @21
    @22
    cA
    wcel
    #
    wa
    #
    @22
    @26
    cA
    cres
    #
    cfv
    #
    @24
    @27
    @62
    @22
    @63
    @23
    @62
    vk
    cB
    cA
    cC
    wph
    @12
    @20
    @61
    sumss.1
    ad2antrr
    resmptd
    fveq1d
    @61
    @64
    @27
    wceq
    @21
    @22
    cA
    @26
    fvres
    adantl
    eqtr3d
    sumeq2dv
    @21
    cA
    @27
    @29
    @32
    vm
    vn
    @7
    @29
    cres
    #
    @31
    @22
    @31
    @26
    fveq2
    #
    @21
    @6
    cB
    cA
    @7
    @21
    c1
    @4
    fzfid
    #
    @37
    fisuppfi
    @21
    @29
    @7
    @29
    cima
    #
    @65
    wf1o
    #
    @29
    cA
    @65
    wf1o
    #
    @21
    @6
    cB
    @7
    wf1
    #
    @29
    @6
    wss
    @69
    @21
    @8
    @71
    @36
    @6
    cB
    @7
    f1of1
    syl
    @38
    @6
    cB
    @29
    @7
    f1ores
    syl2anc
    @21
    @68
    cA
    wceq
    #
    @69
    @70
    wb
    @21
    @6
    cB
    @7
    wfo
    #
    @12
    @72
    @21
    @8
    @73
    @36
    @6
    cB
    @7
    f1ofo
    syl
    wph
    @12
    @20
    sumss.1
    adantr
    #
    @6
    cB
    cA
    @7
    foimacnv
    syl2anc
    @68
    cA
    @29
    @65
    f1oeq3
    syl
    mpbid
    @39
    @30
    @65
    cfv
    @31
    wceq
    @21
    @30
    @29
    @7
    fvres
    adantl
    @21
    @61
    @22
    cB
    wcel
    @27
    cc
    wcel
    @21
    cA
    cB
    @22
    @74
    sselda
    @21
    cB
    cc
    @22
    @26
    @51
    ffvelrnda
    #
    syldan
    fsumf1o
    eqtrd
    @21
    cB
    @27
    @6
    @32
    vm
    vn
    @7
    @31
    @66
    @67
    @36
    @21
    @41
    wa
    @31
    eqidd
    @75
    fsumf1o
    3eqtr4d
    cA
    cC
    vm
    vk
    sumfc
    cB
    cC
    vm
    vk
    sumfc
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
    fsumss.4
    cB
    vf
    fz1f1o
    syl
    mpjaod
end
