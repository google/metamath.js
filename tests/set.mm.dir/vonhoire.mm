include "c0.mm"
include "wceq.mm"
include "cico.mm"
include "co.mm"
include "cixp.mm"
include "cvoln.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "adantl.mm"
include "cdm.mm"
include "ixpeq1.mm"
include "cfn.mm"
include "0fin.mm"
include "a1i.mm"
include "eqid.mm"
include "cv.mm"
include "noel.mm"
include "pm2.21i.mm"
include "hoimbl2.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "von0val.mm"
include "eqtrd.mm"
include "0red.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "cmpt.mm"
include "cvol.mm"
include "cprod.mm"
include "csb.mm"
include "simpr.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfcsb1.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "nfel.mm"
include "oveq12d.mm"
include "ixpeq2dva.mm"
include "nfov.mm"
include "cbvixp.mm"
include "eqcomi.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "wf.mm"
include "fmptdf.mm"
include "vonn0hoi.mm"
include "volicore.mm"
include "fprodrecl.mm"
include "syldan.mm"
include "pm2.61dan.mm"

theorem vonhoire
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cX: class X
  let vj: setvar j
  let vx: setvar x
  assume vonhoire.n: |- F/ k ph
  assume vonhoire.x: |- ( ph -> X e. Fin )
  assume vonhoire.a: |- ( ( ph /\ k e. X ) -> A e. RR )
  assume vonhoire.b: |- ( ( ph /\ k e. X ) -> B e. RR )

  disjoint X k
  disjoint A j
  disjoint B j
  disjoint X j
  disjoint j k
  disjoint j ph
  disjoint k x
  assert |- ( ph -> ( ( voln ` X ) ` X_ k e. X ( A [,) B ) ) e. RR )

  proof
    wph
    cX
    c0
    wceq
    #
    vk
    cX
    cA
    cB
    cico
    co
    #
    cixp
    #
    cX
    cvoln
    cfv
    #
    cfv
    #
    cr
    wcel
    #
    wph
    @0
    wa
    #
    @4
    cc0
    cr
    @6
    @4
    @2
    c0
    cvoln
    cfv
    #
    cfv
    #
    cc0
    @0
    @4
    @8
    wceq
    wph
    @0
    @2
    @3
    @7
    cX
    c0
    cvoln
    fveq2
    fveq1d
    adantl
    @6
    @2
    @6
    @2
    vk
    c0
    @1
    cixp
    #
    @7
    cdm
    #
    @0
    @2
    @9
    wceq
    wph
    vk
    cX
    c0
    @1
    ixpeq1
    adantl
    wph
    @9
    @10
    wcel
    @0
    wph
    cA
    cB
    @10
    vk
    c0
    vonhoire.n
    c0
    cfn
    wcel
    wph
    0fin
    a1i
    @10
    eqid
    vk
    cv
    #
    c0
    wcel
    #
    cA
    cr
    wcel
    #
    wph
    @12
    @13
    @11
    noel
    #
    pm2.21i
    adantl
    @12
    cB
    cr
    wcel
    #
    wph
    @12
    @15
    @14
    pm2.21i
    adantl
    hoimbl2
    adantr
    eqeltrd
    von0val
    eqtrd
    @6
    0red
    eqeltrd
    wph
    @0
    wn
    #
    cX
    c0
    wne
    #
    @5
    @16
    @17
    wph
    cX
    c0
    neqne
    adantl
    wph
    @17
    wa
    #
    @4
    cX
    vj
    cv
    #
    vk
    cX
    cA
    cmpt
    #
    cfv
    #
    @19
    vk
    cX
    cB
    cmpt
    #
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    vj
    cprod
    #
    cr
    @18
    @4
    vj
    cX
    @24
    cixp
    #
    @3
    cfv
    #
    @26
    wph
    @4
    @28
    wceq
    @17
    wph
    @2
    @27
    @3
    wph
    @27
    vj
    cX
    vk
    @19
    cA
    csb
    #
    vk
    @19
    cB
    csb
    #
    cico
    co
    #
    cixp
    #
    @2
    wph
    vj
    cX
    @24
    @31
    wph
    @19
    cX
    wcel
    #
    wa
    #
    @21
    @29
    @23
    @30
    cico
    @34
    @33
    @29
    cr
    wcel
    #
    @21
    @29
    wceq
    wph
    @33
    simpr
    #
    wph
    @11
    cX
    wcel
    #
    wa
    #
    @13
    wi
    @34
    @35
    wi
    vk
    vj
    @34
    @35
    vk
    wph
    @33
    vk
    vonhoire.n
    @33
    vk
    nfv
    nfan
    #
    vk
    @29
    cr
    vk
    @19
    cA
    vk
    @19
    nfcv
    #
    nfcsb1
    #
    nfel1
    nfim
    @11
    @19
    wceq
    #
    @38
    @34
    @13
    @35
    @42
    @37
    @33
    wph
    @11
    @19
    cX
    eleq1
    anbi2d
    #
    @42
    cA
    @29
    cr
    vk
    @19
    cA
    csbeq1a
    #
    eleq1d
    imbi12d
    vonhoire.a
    chvar
    #
    vk
    @19
    cA
    @29
    cX
    @20
    cr
    @40
    @41
    @44
    @20
    eqid
    #
    fvmptf
    syl2anc
    #
    @34
    @33
    @30
    cr
    wcel
    #
    @23
    @30
    wceq
    @36
    @38
    @15
    wi
    @34
    @48
    wi
    vk
    vj
    @34
    @48
    vk
    @39
    vk
    @30
    cr
    vk
    @19
    cB
    @40
    nfcsb1
    #
    vk
    cr
    nfcv
    nfel
    nfim
    @42
    @38
    @34
    @15
    @48
    @43
    @42
    cB
    @30
    cr
    vk
    @19
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    vonhoire.b
    chvar
    #
    vk
    @19
    cB
    @30
    cX
    @22
    cr
    @40
    @49
    @50
    @22
    eqid
    #
    fvmptf
    syl2anc
    #
    oveq12d
    ixpeq2dva
    @32
    @2
    wceq
    wph
    @2
    @32
    vk
    vj
    cX
    @1
    @31
    vj
    @1
    nfcv
    vk
    @29
    @30
    cico
    @41
    vk
    cico
    nfcv
    @49
    nfov
    @42
    cA
    @29
    cB
    @30
    cico
    @44
    @50
    oveq12d
    cbvixp
    eqcomi
    a1i
    eqtr2d
    fveq2d
    adantr
    @18
    @20
    @22
    vj
    @27
    cX
    wph
    cX
    cfn
    wcel
    @17
    vonhoire.x
    adantr
    wph
    @17
    simpr
    wph
    cX
    cr
    @20
    wf
    @17
    wph
    vk
    cX
    cA
    cr
    @20
    vonhoire.n
    vonhoire.a
    @46
    fmptdf
    adantr
    wph
    cX
    cr
    @22
    wf
    @17
    wph
    vk
    cX
    cB
    cr
    @22
    vonhoire.n
    vonhoire.b
    @52
    fmptdf
    adantr
    @27
    eqid
    vonn0hoi
    eqtrd
    wph
    @26
    cr
    wcel
    @17
    wph
    cX
    @25
    vj
    vonhoire.x
    @34
    @21
    cr
    wcel
    @23
    cr
    wcel
    @25
    cr
    wcel
    @34
    @21
    @29
    cr
    @47
    @45
    eqeltrd
    @34
    @23
    @30
    cr
    @53
    @51
    eqeltrd
    @21
    @23
    volicore
    syl2anc
    fprodrecl
    adantr
    eqeltrd
    syldan
    pm2.61dan
end
