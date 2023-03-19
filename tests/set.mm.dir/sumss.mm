include "cz.mm"
include "wcel.mm"
include "csu.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "caddc.mm"
include "cuz.mm"
include "cc0.mm"
include "cif.mm"
include "cseq.mm"
include "cli.mm"
include "eqid.mm"
include "simpr.mm"
include "wss.mm"
include "sstrd.mm"
include "adantr.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfv.mm"
include "nfif.mm"
include "nfeq.mm"
include "fveq2.mm"
include "eleq1.mm"
include "ifbieq1d.mm"
include "eqeq12d.mm"
include "cid.mm"
include "fvmpt2i.mm"
include "iftrue.mm"
include "fveq2d.mm"
include "sylan9eq.mm"
include "eqtrd.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "wn.mm"
include "iffalse.mm"
include "0z.mm"
include "fvi.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "pm2.61dan.mm"
include "vtoclgaf.mm"
include "cc.mm"
include "wf.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "zsum.mm"
include "wi.mm"
include "nfim.mm"
include "imbi2d.mm"
include "adantll.mm"
include "sselda.mm"
include "syl.mm"
include "ad2antrl.mm"
include "cdif.mm"
include "eldif.mm"
include "0cn.mm"
include "sylan2br.mm"
include "expr.mm"
include "a1d.mm"
include "imp.mm"
include "expcom.mm"
include "impcom.mm"
include "adantlr.mm"
include "ex.mm"
include "syl6eqel.mm"
include "pm2.61d.mm"
include "sumfc.mm"
include "3eqtr3g.mm"
include "c0.mm"
include "cdm.mm"
include "cpw.mm"
include "uzf.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "sseq2d.mm"
include "syl5ib.mm"
include "ss0.mm"
include "sumeq1d.mm"

theorem sumss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cM: class M
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  assume sumss.1: |- ( ph -> A C_ B )
  assume sumss.2: |- ( ( ph /\ k e. A ) -> C e. CC )
  assume sumss.3: |- ( ( ph /\ k e. ( B \ A ) ) -> C = 0 )
  assume sumss.4: |- ( ph -> B C_ ( ZZ>= ` M ) )

  disjoint A k
  disjoint B k
  disjoint k ph
  disjoint M k
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
  disjoint M m
  assert |- ( ph -> sum_ k e. A C = sum_ k e. B C )

  proof
    wph
    cM
    cz
    wcel
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
    wph
    @0
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
    @4
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
    @3
    @7
    caddc
    vk
    cM
    cuz
    cfv
    #
    vk
    cv
    #
    cA
    wcel
    #
    cC
    cc0
    cif
    #
    cmpt
    #
    cM
    cseq
    cli
    cfv
    @10
    @3
    cA
    @6
    vm
    @15
    cM
    @11
    @11
    eqid
    #
    wph
    @0
    simpr
    #
    wph
    cA
    @11
    wss
    @0
    wph
    cA
    cB
    @11
    sumss.1
    sumss.4
    sstrd
    adantr
    @4
    @11
    wcel
    #
    @4
    @15
    cfv
    #
    @4
    cA
    wcel
    #
    @6
    cc0
    cif
    #
    wceq
    #
    @3
    @12
    @15
    cfv
    #
    @13
    @12
    @5
    cfv
    #
    cc0
    cif
    #
    wceq
    #
    @22
    vk
    @4
    @11
    vk
    @4
    nfcv
    #
    vk
    @19
    @21
    vk
    @11
    @14
    @4
    nffvmpt1
    #
    @20
    vk
    @6
    cc0
    @20
    vk
    nfv
    vk
    cA
    cC
    @4
    nffvmpt1
    vk
    cc0
    nfcv
    #
    nfif
    nfeq
    @12
    @4
    wceq
    #
    @23
    @19
    @25
    @21
    @12
    @4
    @15
    fveq2
    #
    @30
    @13
    @20
    @24
    @6
    cc0
    @12
    @4
    cA
    eleq1
    @12
    @4
    @5
    fveq2
    ifbieq1d
    eqeq12d
    @12
    @11
    wcel
    #
    @13
    @26
    @32
    @13
    wa
    @23
    cC
    cid
    cfv
    #
    @25
    @32
    @13
    @23
    @14
    cid
    cfv
    #
    @33
    vk
    @11
    @14
    @15
    @15
    eqid
    fvmpt2i
    #
    @13
    @14
    cC
    cid
    @13
    cC
    cc0
    iftrue
    fveq2d
    sylan9eq
    #
    @13
    @25
    @33
    wceq
    @32
    @13
    @25
    @24
    @33
    @13
    @24
    cc0
    iftrue
    vk
    cA
    cC
    @5
    @5
    eqid
    #
    fvmpt2i
    eqtrd
    adantl
    eqtr4d
    @32
    @13
    wn
    #
    wa
    @23
    cc0
    @25
    @32
    @38
    @23
    @34
    cc0
    @35
    @38
    @34
    cc0
    cid
    cfv
    #
    cc0
    @38
    @14
    cc0
    cid
    @13
    cC
    cc0
    iffalse
    fveq2d
    cc0
    cz
    wcel
    @39
    cc0
    wceq
    #
    0z
    cc0
    cz
    fvi
    ax-mp
    syl6eq
    sylan9eq
    #
    @38
    @25
    cc0
    wceq
    @32
    @13
    @24
    cc0
    iffalse
    adantl
    eqtr4d
    pm2.61dan
    vtoclgaf
    adantl
    @3
    cA
    cc
    @4
    @5
    wph
    cA
    cc
    @5
    wf
    @0
    wph
    vk
    cA
    cC
    cc
    @5
    sumss.2
    @37
    fmptd
    adantr
    ffvelrnda
    zsum
    @3
    cB
    @9
    vm
    @15
    cM
    @11
    @16
    @17
    wph
    cB
    @11
    wss
    #
    @0
    sumss.4
    adantr
    wph
    @18
    @19
    @4
    cB
    wcel
    #
    @9
    cc0
    cif
    #
    wceq
    #
    @0
    @18
    wph
    @45
    wph
    @23
    @12
    cB
    wcel
    #
    @12
    @8
    cfv
    #
    cc0
    cif
    #
    wceq
    #
    wi
    wph
    @45
    wi
    vk
    @4
    @11
    @27
    wph
    @45
    vk
    wph
    vk
    nfv
    vk
    @19
    @44
    @28
    @43
    vk
    @9
    cc0
    @43
    vk
    nfv
    vk
    cB
    cC
    @4
    nffvmpt1
    @29
    nfif
    nfeq
    nfim
    @30
    @49
    @45
    wph
    @30
    @23
    @19
    @48
    @44
    @31
    @30
    @46
    @43
    @47
    @9
    cc0
    @12
    @4
    cB
    eleq1
    @12
    @4
    @8
    fveq2
    ifbieq1d
    eqeq12d
    imbi2d
    wph
    @32
    @49
    wph
    @32
    wa
    #
    @13
    @49
    @50
    @13
    wa
    #
    @23
    @33
    @48
    @32
    @13
    @23
    @33
    wceq
    wph
    @36
    adantll
    @51
    @46
    @48
    @33
    wceq
    #
    @50
    cA
    cB
    @12
    wph
    cA
    cB
    wss
    #
    @32
    sumss.1
    adantr
    sselda
    @46
    @48
    @47
    @33
    @46
    @47
    cc0
    iftrue
    vk
    cB
    cC
    @8
    @8
    eqid
    #
    fvmpt2i
    eqtrd
    #
    syl
    eqtr4d
    @50
    @38
    wa
    @23
    cc0
    @48
    @32
    @38
    @23
    cc0
    wceq
    wph
    @41
    adantll
    @50
    @38
    @48
    cc0
    wceq
    #
    wph
    @38
    @56
    wi
    #
    @32
    wph
    @46
    @57
    wph
    @46
    @38
    @56
    wph
    @46
    @38
    wa
    #
    wa
    @48
    @33
    cc0
    @46
    @52
    wph
    @38
    @55
    ad2antrl
    @58
    wph
    @12
    cB
    cA
    cdif
    wcel
    #
    @33
    cc0
    wceq
    @12
    cB
    cA
    eldif
    #
    wph
    @59
    wa
    #
    @33
    @39
    cc0
    @61
    cC
    cc0
    cid
    sumss.3
    fveq2d
    cc0
    cc
    wcel
    @40
    0cn
    cc0
    cc
    fvi
    ax-mp
    syl6eq
    sylan2br
    eqtrd
    expr
    wph
    @46
    wn
    #
    wa
    @56
    @38
    @62
    @56
    wph
    @46
    @47
    cc0
    iffalse
    adantl
    a1d
    pm2.61dan
    adantr
    imp
    eqtr4d
    pm2.61dan
    expcom
    vtoclgaf
    impcom
    adantlr
    @3
    cB
    cc
    @4
    @8
    wph
    cB
    cc
    @8
    wf
    @0
    wph
    vk
    cB
    cC
    cc
    @8
    wph
    @46
    wa
    @13
    cC
    cc
    wcel
    #
    wph
    @13
    @63
    wi
    @46
    wph
    @13
    @63
    sumss.2
    ex
    adantr
    wph
    @46
    @38
    @63
    @58
    wph
    @59
    @63
    @60
    @61
    cC
    cc0
    cc
    sumss.3
    0cn
    syl6eqel
    sylan2br
    expr
    pm2.61d
    @54
    fmptd
    adantr
    ffvelrnda
    zsum
    eqtr4d
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
    wph
    @0
    wn
    #
    wa
    #
    cA
    cB
    cC
    vk
    @65
    cA
    c0
    cB
    @65
    cA
    c0
    wss
    cA
    c0
    wceq
    @65
    cA
    cB
    c0
    wph
    @53
    @64
    sumss.1
    adantr
    @64
    wph
    cB
    c0
    wss
    #
    wph
    @42
    @64
    @66
    sumss.4
    @64
    @11
    c0
    cB
    @0
    cM
    cuz
    cdm
    #
    wcel
    @11
    c0
    wceq
    @67
    cz
    cM
    cz
    cz
    cpw
    cuz
    uzf
    fdmi
    eleq2i
    cM
    cuz
    ndmfv
    sylnbir
    sseq2d
    syl5ib
    impcom
    #
    sstrd
    cA
    ss0
    syl
    @65
    @66
    cB
    c0
    wceq
    @68
    cB
    ss0
    syl
    eqtr4d
    sumeq1d
    pm2.61dan
end
