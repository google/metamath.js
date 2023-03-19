include "cz.mm"
include "wcel.mm"
include "cprod.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "cmul.mm"
include "cuz.mm"
include "c1.mm"
include "cif.mm"
include "cseq.mm"
include "cli.mm"
include "eqid.mm"
include "simpr.mm"
include "cc0.mm"
include "wne.mm"
include "wbr.mm"
include "wex.mm"
include "wrex.mm"
include "adantr.mm"
include "wss.mm"
include "sstrd.mm"
include "csb.mm"
include "cc.mm"
include "iftrue.mm"
include "adantl.mm"
include "wral.mm"
include "wi.mm"
include "ex.mm"
include "wn.mm"
include "cdif.mm"
include "eldif.mm"
include "ax-1cn.mm"
include "syl6eqel.mm"
include "sylan2br.mm"
include "expr.mm"
include "pm2.61d.mm"
include "ralrimiva.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "weq.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "mpan9.mm"
include "eqeltrd.mm"
include "iffalse.mm"
include "pm2.61dan.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfif.mm"
include "eleq1.mm"
include "ifbieq1d.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "sselda.mm"
include "adantlr.mm"
include "syldan.mm"
include "fvmpts.mm"
include "eqtrd.mm"
include "nfeq1.mm"
include "eqeq1d.mm"
include "eqtr4d.mm"
include "ssneld.mm"
include "imp.mm"
include "syl.mm"
include "wf.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "zprod.mm"
include "ancoms.mm"
include "sylan.mm"
include "ifeq1d.mm"
include "prodfc.mm"
include "3eqtr3g.mm"
include "c0.mm"
include "cdm.mm"
include "cpw.mm"
include "uzf.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "sseqtrd.mm"
include "ss0.mm"
include "prodeq1d.mm"

theorem prodss
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vn: setvar n
  let cM: class M
  let vm: setvar m
  assume prodss.1: |- ( ph -> A C_ B )
  assume prodss.2: |- ( ( ph /\ k e. A ) -> C e. CC )
  assume prodss.3: |- ( ph -> E. n e. ( ZZ>= ` M ) E. y ( y =/= 0 /\ seq n ( x. , ( k e. ( ZZ>= ` M ) |-> if ( k e. B , C , 1 ) ) ) ~~> y ) )
  assume prodss.4: |- ( ( ph /\ k e. ( B \ A ) ) -> C = 1 )
  assume prodss.5: |- ( ph -> B C_ ( ZZ>= ` M ) )

  disjoint A k
  disjoint A n
  disjoint A y
  disjoint B k
  disjoint B n
  disjoint B y
  disjoint C n
  disjoint C y
  disjoint k n
  disjoint k ph
  disjoint k y
  disjoint M n
  disjoint M y
  disjoint n ph
  disjoint n y
  disjoint ph y
  disjoint M k
  disjoint A m
  disjoint B m
  disjoint C m
  disjoint k m
  disjoint M m
  disjoint m n
  disjoint m ph
  disjoint m y
  assert |- ( ph -> prod_ k e. A C = prod_ k e. B C )

  proof
    wph
    cM
    cz
    wcel
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
    cprod
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
    cprod
    #
    @1
    @2
    @3
    @7
    cmul
    vk
    cM
    cuz
    cfv
    #
    vk
    cv
    #
    cB
    wcel
    #
    cC
    c1
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
    vy
    cA
    @6
    vm
    vn
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
    vy
    cv
    #
    cc0
    wne
    cmul
    @15
    vn
    cv
    cseq
    @18
    cli
    wbr
    wa
    vy
    wex
    vn
    @11
    wrex
    @0
    prodss.3
    adantr
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
    prodss.1
    prodss.5
    sstrd
    adantr
    @3
    @4
    @11
    wcel
    #
    wa
    #
    @4
    @15
    cfv
    #
    @4
    cB
    wcel
    #
    vk
    @4
    cC
    csb
    #
    c1
    cif
    #
    @4
    cA
    wcel
    #
    @6
    c1
    cif
    #
    @21
    @20
    @25
    cc
    wcel
    #
    @22
    @25
    wceq
    #
    @3
    @20
    simpr
    @3
    @28
    @20
    wph
    @28
    @0
    wph
    @23
    @28
    wph
    @23
    wa
    @25
    @24
    cc
    @23
    @25
    @24
    wceq
    #
    wph
    @23
    @24
    c1
    iftrue
    #
    adantl
    wph
    cC
    cc
    wcel
    #
    vk
    cB
    wral
    @23
    @24
    cc
    wcel
    #
    wph
    @32
    vk
    cB
    wph
    @13
    wa
    @12
    cA
    wcel
    #
    @32
    wph
    @34
    @32
    wi
    @13
    wph
    @34
    @32
    prodss.2
    ex
    adantr
    wph
    @13
    @34
    wn
    #
    @32
    @13
    @35
    wa
    wph
    @12
    cB
    cA
    cdif
    #
    wcel
    #
    @32
    @12
    cB
    cA
    eldif
    wph
    @37
    wa
    cC
    c1
    cc
    prodss.4
    ax-1cn
    syl6eqel
    sylan2br
    expr
    pm2.61d
    #
    ralrimiva
    @32
    @33
    vk
    @4
    cB
    vk
    @24
    cc
    vk
    @4
    cC
    nfcsb1v
    #
    nfel1
    vk
    vm
    weq
    #
    cC
    @24
    cc
    vk
    @4
    cC
    csbeq1a
    #
    eleq1d
    rspc
    mpan9
    #
    eqeltrd
    @23
    wn
    #
    @28
    wph
    @43
    @25
    c1
    cc
    @23
    @24
    c1
    iffalse
    #
    ax-1cn
    syl6eqel
    adantl
    pm2.61dan
    adantr
    #
    adantr
    vk
    @4
    @14
    @25
    @11
    @15
    cc
    vk
    @4
    nfcv
    @23
    vk
    @24
    c1
    @23
    vk
    nfv
    @39
    vk
    c1
    nfcv
    nfif
    @40
    @13
    @23
    cC
    @24
    c1
    @12
    @4
    cB
    eleq1
    @41
    ifbieq1d
    @15
    eqid
    fvmptf
    #
    syl2anc
    @3
    @27
    @25
    wceq
    #
    @20
    @3
    @23
    @47
    @3
    @23
    wa
    #
    @27
    @24
    @25
    @48
    @26
    @27
    @24
    wceq
    #
    @3
    @26
    @49
    wi
    @23
    @3
    @26
    @49
    @3
    @26
    wa
    #
    @27
    @6
    @24
    @26
    @27
    @6
    wceq
    @3
    @26
    @6
    c1
    iftrue
    adantl
    @50
    @26
    @33
    @6
    @24
    wceq
    @3
    @26
    simpr
    @3
    @26
    @23
    @33
    @3
    cA
    cB
    @4
    wph
    cA
    cB
    wss
    #
    @0
    prodss.1
    adantr
    #
    sselda
    wph
    @23
    @33
    @0
    @42
    adantlr
    #
    syldan
    vk
    @4
    cC
    cA
    @5
    cc
    @5
    eqid
    #
    fvmpts
    syl2anc
    eqtrd
    ex
    adantr
    @3
    @23
    @26
    wn
    #
    @49
    @3
    @23
    @55
    wa
    #
    wa
    @27
    c1
    @24
    @56
    @27
    c1
    wceq
    #
    @3
    @55
    @57
    @23
    @26
    @6
    c1
    iffalse
    #
    adantl
    adantl
    @56
    @3
    @4
    @36
    wcel
    #
    @24
    c1
    wceq
    #
    @4
    cB
    cA
    eldif
    @3
    cC
    c1
    wceq
    #
    vk
    @36
    wral
    #
    @59
    @60
    wph
    @62
    @0
    wph
    @61
    vk
    @36
    prodss.4
    ralrimiva
    adantr
    @61
    @60
    vk
    @4
    @36
    vk
    @24
    c1
    @39
    nfeq1
    @40
    cC
    @24
    c1
    @41
    eqeq1d
    rspc
    mpan9
    sylan2br
    eqtr4d
    expr
    pm2.61d
    @23
    @30
    @3
    @31
    adantl
    eqtr4d
    @3
    @43
    wa
    #
    @27
    c1
    @25
    @63
    @55
    @57
    @3
    @43
    @55
    @3
    cA
    cB
    @4
    @52
    ssneld
    imp
    @58
    syl
    @43
    @25
    c1
    wceq
    @3
    @44
    adantl
    eqtr4d
    pm2.61dan
    adantr
    eqtr4d
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
    prodss.2
    @54
    fmptd
    adantr
    ffvelrnda
    zprod
    @3
    vy
    cB
    @9
    vm
    vn
    @15
    cM
    @11
    @16
    @17
    @19
    wph
    cB
    @11
    wss
    #
    @0
    prodss.5
    adantr
    @21
    @22
    @25
    @23
    @9
    c1
    cif
    #
    @3
    @28
    @20
    @29
    @45
    @20
    @28
    @29
    @46
    ancoms
    sylan
    @21
    @23
    @65
    @25
    wceq
    #
    @3
    @23
    @66
    @20
    @48
    @23
    @9
    @24
    c1
    @48
    @23
    @33
    @9
    @24
    wceq
    @3
    @23
    simpr
    @53
    vk
    @4
    cC
    cB
    @8
    cc
    @8
    eqid
    #
    fvmpts
    syl2anc
    ifeq1d
    adantlr
    @43
    @66
    @21
    @43
    @65
    c1
    @25
    @23
    @9
    c1
    iffalse
    @44
    eqtr4d
    adantl
    pm2.61dan
    eqtr4d
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
    @38
    @67
    fmptd
    adantr
    ffvelrnda
    zprod
    eqtr4d
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
    @69
    cA
    c0
    cB
    @69
    cA
    c0
    wss
    cA
    c0
    wceq
    @69
    cA
    cB
    c0
    wph
    @51
    @68
    prodss.1
    adantr
    @69
    cB
    @11
    c0
    wph
    @64
    @68
    prodss.5
    adantr
    @68
    @11
    c0
    wceq
    #
    wph
    @0
    cM
    cuz
    cdm
    #
    wcel
    @70
    @71
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
    adantl
    sseqtrd
    #
    sstrd
    cA
    ss0
    syl
    @69
    cB
    c0
    wss
    cB
    c0
    wceq
    @72
    cB
    ss0
    syl
    eqtr4d
    prodeq1d
    pm2.61dan
end
