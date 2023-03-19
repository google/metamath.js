include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "wb.mm"
include "citg.mm"
include "wceq.mm"
include "cv.mm"
include "cc0.mm"
include "cif.mm"
include "wa.mm"
include "csb.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfif.mm"
include "eleq1.mm"
include "csbeq1a.mm"
include "ifbieq1d.mm"
include "cbvmpt.mm"
include "cc.mm"
include "wss.mm"
include "adantr.mm"
include "cvol.mm"
include "cdm.mm"
include "cmbf.mm"
include "iftrue.mm"
include "mpteq2ia.mm"
include "eqtr4i.mm"
include "simpr.mm"
include "syl5eqelr.mm"
include "iblmbf.mm"
include "syl.mm"
include "wf.mm"
include "wral.mm"
include "sselda.mm"
include "syldan.mm"
include "eqid.mm"
include "fmptd.mm"
include "feq1i.mm"
include "sylib.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "mbfdm2.mm"
include "cdif.mm"
include "cun.mm"
include "undif.mm"
include "id.mm"
include "cr.mm"
include "covol.mm"
include "cfv.mm"
include "ssdifssd.mm"
include "nulmbl.mm"
include "syl2anc.mm"
include "unmbl.mm"
include "syl2anr.mm"
include "eqeltrrd.mm"
include "wn.mm"
include "eldifn.mm"
include "adantl.mm"
include "iffalsed.mm"
include "iblss2.mm"
include "syl5eqel.mm"
include "eqtr3i.mm"
include "0cn.mm"
include "ifcl.mm"
include "sylancl.mm"
include "dfss4.mm"
include "difmbl.mm"
include "iblss.mm"
include "impbida.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "itgeqa.mm"
include "simpld.mm"
include "bitrd.mm"
include "itgss2.mm"
include "simprd.mm"
include "eqtrd.mm"
include "jca.mm"

theorem itgss3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume itgss3.1: |- ( ph -> A C_ B )
  assume itgss3.2: |- ( ph -> B C_ RR )
  assume itgss3.3: |- ( ph -> ( vol* ` ( B \ A ) ) = 0 )
  assume itgss3.4: |- ( ( ph /\ x e. B ) -> C e. CC )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint ph y
  assert |- ( ph -> ( ( ( x e. A |-> C ) e. L^1 <-> ( x e. B |-> C ) e. L^1 ) /\ S. A C _d x = S. B C _d x ) )

  proof
    wph
    vx
    cA
    cC
    cmpt
    #
    cibl
    wcel
    #
    vx
    cB
    cC
    cmpt
    cibl
    wcel
    #
    wb
    vx
    cA
    cC
    citg
    #
    vx
    cB
    cC
    citg
    #
    wceq
    wph
    @1
    vx
    cB
    vx
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
    cibl
    wcel
    #
    @2
    wph
    @1
    @9
    wph
    @1
    wa
    #
    @8
    vy
    cB
    vy
    cv
    #
    cA
    wcel
    #
    vx
    @11
    cC
    csb
    #
    cc0
    cif
    #
    cmpt
    #
    cibl
    vx
    vy
    cB
    @7
    @14
    vy
    @7
    nfcv
    #
    @12
    vx
    @13
    cc0
    @12
    vx
    nfv
    vx
    @11
    cC
    nfcsb1v
    #
    vx
    cc0
    nfcv
    nfif
    #
    @5
    @11
    wceq
    @6
    @12
    cC
    @13
    cc0
    @5
    @11
    cA
    eleq1
    vx
    @11
    cC
    csbeq1a
    #
    ifbieq1d
    #
    cbvmpt
    #
    @10
    vy
    cA
    cB
    @14
    cc
    wph
    cA
    cB
    wss
    #
    @1
    itgss3.1
    adantr
    wph
    @1
    cA
    cvol
    cdm
    #
    wcel
    #
    cB
    @23
    wcel
    #
    @10
    vy
    cA
    @14
    cc
    @10
    vy
    cA
    @14
    cmpt
    #
    cibl
    wcel
    @26
    cmbf
    wcel
    @10
    @26
    @0
    cibl
    @0
    vy
    cA
    @13
    cmpt
    @26
    vx
    vy
    cA
    cC
    @13
    vy
    cC
    nfcv
    @17
    @19
    cbvmpt
    vy
    cA
    @14
    @13
    @12
    @13
    cc0
    iftrue
    mpteq2ia
    eqtr4i
    #
    wph
    @1
    simpr
    syl5eqelr
    #
    @26
    iblmbf
    syl
    @10
    @14
    cc
    wcel
    #
    vy
    cA
    @10
    cA
    cc
    @26
    wf
    #
    @29
    vy
    cA
    wral
    @10
    cA
    cc
    @0
    wf
    #
    @30
    wph
    @31
    @1
    wph
    vx
    cA
    cC
    cc
    @0
    wph
    @6
    @5
    cB
    wcel
    #
    cC
    cc
    wcel
    #
    wph
    cA
    cB
    @5
    itgss3.1
    sselda
    itgss3.4
    syldan
    @0
    eqid
    fmptd
    adantr
    cA
    cc
    @0
    @26
    @27
    feq1i
    sylib
    vy
    cA
    cc
    @14
    @26
    @26
    eqid
    fmpt
    sylibr
    r19.21bi
    #
    mbfdm2
    wph
    @24
    wa
    cA
    cB
    cA
    cdif
    #
    cun
    #
    cB
    @23
    wph
    @36
    cB
    wceq
    #
    @24
    wph
    @22
    @37
    itgss3.1
    cA
    cB
    undif
    sylib
    adantr
    @24
    @24
    @35
    @23
    wcel
    #
    @36
    @23
    wcel
    wph
    @24
    id
    wph
    @35
    cr
    wss
    @35
    covol
    cfv
    cc0
    wceq
    @38
    wph
    cB
    cr
    cA
    itgss3.2
    ssdifssd
    #
    itgss3.3
    @35
    nulmbl
    syl2anc
    #
    cA
    @35
    unmbl
    syl2anr
    eqeltrrd
    syldan
    @34
    @10
    @11
    @35
    wcel
    #
    wa
    @12
    @13
    cc0
    @41
    @12
    wn
    @10
    @11
    cB
    cA
    eldifn
    adantl
    iffalsed
    @28
    iblss2
    syl5eqel
    wph
    @9
    wa
    #
    @0
    @26
    cibl
    vx
    cA
    @7
    cmpt
    @0
    @26
    vx
    cA
    @7
    cC
    @6
    cC
    cc0
    iftrue
    #
    mpteq2ia
    vx
    vy
    cA
    @7
    @14
    @16
    @18
    @20
    cbvmpt
    eqtr3i
    @42
    vy
    cA
    cB
    @14
    cc
    wph
    @22
    @9
    itgss3.1
    adantr
    wph
    @9
    @25
    @24
    @42
    vy
    cB
    @14
    cc
    @42
    @15
    cibl
    wcel
    @15
    cmbf
    wcel
    @42
    @15
    @8
    cibl
    @21
    wph
    @9
    simpr
    syl5eqelr
    #
    @15
    iblmbf
    syl
    @42
    @29
    vy
    cB
    @42
    cB
    cc
    @15
    wf
    #
    @29
    vy
    cB
    wral
    wph
    @45
    @9
    wph
    cB
    cc
    @8
    wf
    @45
    wph
    vx
    cB
    @7
    cc
    @8
    wph
    @32
    wa
    @33
    cc0
    cc
    wcel
    @7
    cc
    wcel
    itgss3.4
    0cn
    @6
    cC
    cc0
    cc
    ifcl
    sylancl
    #
    @8
    eqid
    fmptd
    cB
    cc
    @8
    @15
    @21
    feq1i
    sylib
    adantr
    vy
    cB
    cc
    @14
    @15
    @15
    eqid
    fmpt
    sylibr
    r19.21bi
    #
    mbfdm2
    wph
    @25
    wa
    cB
    @35
    cdif
    #
    cA
    @23
    wph
    @48
    cA
    wceq
    #
    @25
    wph
    @22
    @49
    itgss3.1
    cA
    cB
    dfss4
    sylib
    #
    adantr
    @25
    @25
    @38
    @48
    @23
    wcel
    wph
    @25
    id
    @40
    cB
    @35
    difmbl
    syl2anr
    eqeltrrd
    syldan
    @47
    @44
    iblss
    syl5eqel
    impbida
    wph
    @9
    @2
    wb
    #
    vx
    cB
    @7
    citg
    #
    @4
    wceq
    #
    wph
    vx
    @35
    cB
    @7
    cC
    @46
    itgss3.4
    @39
    itgss3.3
    wph
    @5
    @48
    wcel
    #
    wa
    @6
    @7
    cC
    wceq
    wph
    @54
    @6
    wph
    @48
    cA
    @5
    @50
    eleq2d
    biimpa
    @43
    syl
    itgeqa
    #
    simpld
    bitrd
    wph
    @3
    @52
    @4
    wph
    @22
    @3
    @52
    wceq
    itgss3.1
    vx
    cA
    cB
    cC
    itgss2
    syl
    wph
    @51
    @53
    @55
    simprd
    eqtrd
    jca
end
