include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "cprod.mm"
include "cabs.mm"
include "wceq.mm"
include "syl6eleq.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "prodeq1d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cz.mm"
include "wa.mm"
include "csb.mm"
include "csbfv2g.mm"
include "adantl.mm"
include "csn.mm"
include "fzsn.mm"
include "cc.mm"
include "simpr.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "mpan9.mm"
include "sylan2.mm"
include "abscld.mm"
include "recnd.mm"
include "eqeltrd.mm"
include "prodsns.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"
include "expcom.mm"
include "w3a.mm"
include "cmul.mm"
include "simp3.mm"
include "cvv.mm"
include "ovex.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "a1i.mm"
include "oveq12d.mm"
include "elfzuz.mm"
include "adantlr.mm"
include "fprodp1s.mm"
include "fzfid.mm"
include "fprodcl.mm"
include "peano2uz.mm"
include "absmuld.mm"
include "3adant3.mm"
include "3eqtr4d.mm"
include "3exp.mm"
include "com12.mm"
include "a2d.mm"
include "uzind4.mm"
include "mpcom.mm"

theorem fprodabs
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cM: class M
  let cN: class N
  let cZ: class Z
  let va: setvar a
  let vn: setvar n
  assume fprodabs.1: |- Z = ( ZZ>= ` M )
  assume fprodabs.2: |- ( ph -> N e. Z )
  assume fprodabs.3: |- ( ( ph /\ k e. Z ) -> A e. CC )

  disjoint M k
  disjoint N k
  disjoint Z k
  disjoint k ph
  disjoint A a
  disjoint A n
  disjoint a n
  disjoint M a
  disjoint M n
  disjoint a k
  disjoint k n
  disjoint N a
  disjoint Z a
  disjoint Z n
  disjoint a ph
  disjoint n ph
  assert |- ( ph -> ( abs ` prod_ k e. ( M ... N ) A ) = prod_ k e. ( M ... N ) ( abs ` A ) )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    wph
    cM
    cN
    cfz
    co
    #
    cA
    vk
    cprod
    #
    cabs
    cfv
    #
    @1
    cA
    cabs
    cfv
    #
    vk
    cprod
    #
    wceq
    #
    wph
    cN
    cZ
    @0
    fprodabs.2
    fprodabs.1
    syl6eleq
    wph
    cM
    va
    cv
    #
    cfz
    co
    #
    cA
    vk
    cprod
    #
    cabs
    cfv
    #
    @8
    @4
    vk
    cprod
    #
    wceq
    #
    wi
    wph
    cM
    cM
    cfz
    co
    #
    cA
    vk
    cprod
    #
    cabs
    cfv
    #
    @13
    @4
    vk
    cprod
    #
    wceq
    #
    wi
    wph
    cM
    vn
    cv
    #
    cfz
    co
    #
    cA
    vk
    cprod
    #
    cabs
    cfv
    #
    @19
    @4
    vk
    cprod
    #
    wceq
    #
    wi
    wph
    cM
    @18
    c1
    caddc
    co
    #
    cfz
    co
    #
    cA
    vk
    cprod
    #
    cabs
    cfv
    #
    @25
    @4
    vk
    cprod
    #
    wceq
    #
    wi
    wph
    @6
    wi
    va
    vn
    cM
    cN
    @7
    cM
    wceq
    #
    @12
    @17
    wph
    @30
    @10
    @15
    @11
    @16
    @30
    @9
    @14
    cabs
    @30
    @8
    @13
    cA
    vk
    @7
    cM
    cM
    cfz
    oveq2
    #
    prodeq1d
    fveq2d
    @30
    @8
    @13
    @4
    vk
    @31
    prodeq1d
    eqeq12d
    imbi2d
    va
    vn
    weq
    #
    @12
    @23
    wph
    @32
    @10
    @21
    @11
    @22
    @32
    @9
    @20
    cabs
    @32
    @8
    @19
    cA
    vk
    @7
    @18
    cM
    cfz
    oveq2
    #
    prodeq1d
    fveq2d
    @32
    @8
    @19
    @4
    vk
    @33
    prodeq1d
    eqeq12d
    imbi2d
    @7
    @24
    wceq
    #
    @12
    @29
    wph
    @34
    @10
    @27
    @11
    @28
    @34
    @9
    @26
    cabs
    @34
    @8
    @25
    cA
    vk
    @7
    @24
    cM
    cfz
    oveq2
    #
    prodeq1d
    fveq2d
    @34
    @8
    @25
    @4
    vk
    @35
    prodeq1d
    eqeq12d
    imbi2d
    @7
    cN
    wceq
    #
    @12
    @6
    wph
    @36
    @10
    @3
    @11
    @5
    @36
    @9
    @2
    cabs
    @36
    @8
    @1
    cA
    vk
    @7
    cN
    cM
    cfz
    oveq2
    #
    prodeq1d
    fveq2d
    @36
    @8
    @1
    @4
    vk
    @37
    prodeq1d
    eqeq12d
    imbi2d
    wph
    cM
    cz
    wcel
    #
    @17
    wph
    @38
    wa
    #
    vk
    cM
    @4
    csb
    #
    vk
    cM
    cA
    csb
    #
    cabs
    cfv
    #
    @16
    @15
    @38
    @40
    @42
    wceq
    wph
    vk
    cM
    cA
    cz
    cabs
    csbfv2g
    adantl
    #
    @39
    @16
    cM
    csn
    #
    @4
    vk
    cprod
    #
    @40
    @39
    @13
    @44
    @4
    vk
    @38
    @13
    @44
    wceq
    wph
    cM
    fzsn
    #
    adantl
    prodeq1d
    @39
    @38
    @40
    cc
    wcel
    @45
    @40
    wceq
    wph
    @38
    simpr
    #
    @39
    @40
    @42
    cc
    @43
    @39
    @42
    @39
    @41
    @38
    wph
    cM
    cZ
    wcel
    #
    @41
    cc
    wcel
    #
    @38
    cM
    @0
    cZ
    cM
    uzid
    fprodabs.1
    syl6eleqr
    wph
    cA
    cc
    wcel
    #
    vk
    cZ
    wral
    #
    @48
    @49
    wph
    @50
    vk
    cZ
    fprodabs.3
    ralrimiva
    #
    @50
    @49
    vk
    cM
    cZ
    vk
    @41
    cc
    vk
    cM
    cA
    nfcsb1v
    nfel1
    vk
    cv
    #
    cM
    wceq
    cA
    @41
    cc
    vk
    cM
    cA
    csbeq1a
    eleq1d
    rspc
    mpan9
    sylan2
    #
    abscld
    recnd
    eqeltrd
    @4
    vk
    cM
    cz
    prodsns
    syl2anc
    eqtrd
    @39
    @14
    @41
    cabs
    @39
    @14
    @44
    cA
    vk
    cprod
    #
    @41
    @38
    @14
    @55
    wceq
    wph
    @38
    @13
    @44
    cA
    vk
    @46
    prodeq1d
    adantl
    @39
    @38
    @49
    @55
    @41
    wceq
    @47
    @54
    cA
    vk
    cM
    cz
    prodsns
    syl2anc
    eqtrd
    fveq2d
    3eqtr4rd
    expcom
    @18
    @0
    wcel
    #
    wph
    @23
    @29
    wph
    @56
    @23
    @29
    wi
    wph
    @56
    @23
    @29
    wph
    @56
    @23
    w3a
    #
    @21
    vk
    @24
    cA
    csb
    #
    cabs
    cfv
    #
    cmul
    co
    #
    @22
    vk
    @24
    @4
    csb
    #
    cmul
    co
    #
    @27
    @28
    @57
    @21
    @22
    @59
    @61
    cmul
    wph
    @56
    @23
    simp3
    @59
    @61
    wceq
    @57
    @61
    @59
    @24
    cvv
    wcel
    @61
    @59
    wceq
    @18
    c1
    caddc
    ovex
    vk
    @24
    cA
    cvv
    cabs
    csbfv2g
    ax-mp
    eqcomi
    a1i
    oveq12d
    wph
    @56
    @27
    @60
    wceq
    @23
    wph
    @56
    wa
    #
    @27
    @20
    @58
    cmul
    co
    #
    cabs
    cfv
    @60
    @63
    @26
    @64
    cabs
    @63
    cA
    vk
    cM
    @18
    wph
    @56
    simpr
    #
    wph
    @53
    @25
    wcel
    #
    @50
    @56
    @66
    wph
    @53
    cZ
    wcel
    #
    @50
    @66
    @53
    @0
    cZ
    @53
    cM
    @24
    elfzuz
    fprodabs.1
    syl6eleqr
    fprodabs.3
    sylan2
    adantlr
    #
    fprodp1s
    fveq2d
    @63
    @20
    @58
    @63
    @19
    cA
    vk
    @63
    cM
    @18
    fzfid
    wph
    @53
    @19
    wcel
    #
    @50
    @56
    @69
    wph
    @67
    @50
    @69
    @53
    @0
    cZ
    @53
    cM
    @18
    elfzuz
    fprodabs.1
    syl6eleqr
    fprodabs.3
    sylan2
    adantlr
    fprodcl
    @56
    wph
    @24
    cZ
    wcel
    #
    @58
    cc
    wcel
    #
    @56
    @24
    @0
    cZ
    cM
    @18
    peano2uz
    fprodabs.1
    syl6eleqr
    wph
    @51
    @70
    @71
    @52
    @50
    @71
    vk
    @24
    cZ
    vk
    @58
    cc
    vk
    @24
    cA
    nfcsb1v
    nfel1
    @53
    @24
    wceq
    cA
    @58
    cc
    vk
    @24
    cA
    csbeq1a
    eleq1d
    rspc
    mpan9
    sylan2
    absmuld
    eqtrd
    3adant3
    wph
    @56
    @28
    @62
    wceq
    @23
    @63
    @4
    vk
    cM
    @18
    @65
    @63
    @66
    wa
    #
    @4
    @72
    cA
    @68
    abscld
    recnd
    fprodp1s
    3adant3
    3eqtr4d
    3exp
    com12
    a2d
    uzind4
    mpcom
end
