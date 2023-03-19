include "cmnf.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "crest.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "breq1.mm"
include "rabbidv.mm"
include "adantl.mm"
include "cdm.mm"
include "nfdm.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nfv.mm"
include "nffv.mm"
include "nfbr.mm"
include "fveq2.mm"
include "breq2d.mm"
include "cbvrab.mm"
include "a1i.mm"
include "cr.mm"
include "wf.mm"
include "smff.mm"
include "adantr.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "pimgtmnf.mm"
include "eqidd.mm"
include "3eqtrd.mm"
include "eqtrd.mm"
include "cuni.mm"
include "csalg.mm"
include "smfdmss.mm"
include "restuni4.mm"
include "eqcomd.mm"
include "cvv.mm"
include "csmblfn.mm"
include "dmexd.mm"
include "syl5eqel.mm"
include "eqid.mm"
include "subsalsal.mm"
include "salunid.mm"
include "eqeltrd.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "cpnf.mm"
include "c0.mm"
include "pimgtpnf2.mm"
include "0sald.mm"
include "adantlr.mm"
include "simpll.mm"
include "cxr.mm"
include "syl.mm"
include "simplr.mm"
include "xrred.mm"
include "smfpreimagtf.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"
include "syldan.mm"

theorem smfpimgtxr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cS: class S
  let cF: class F
  let vy: setvar y
  let vk: setvar k
  assume smfpimgtxr.x: |- F/_ x F
  assume smfpimgtxr.s: |- ( ph -> S e. SAlg )
  assume smfpimgtxr.f: |- ( ph -> F e. ( SMblFn ` S ) )
  assume smfpimgtxr.d: |- D = dom F
  assume smfpimgtxr.a: |- ( ph -> A e. RR* )

  disjoint A x
  disjoint D x
  disjoint D y
  disjoint x y
  disjoint F y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> { x e. D | A < ( F ` x ) } e. ( S |`t D ) )

  proof
    wph
    cA
    cmnf
    wceq
    #
    cA
    vx
    cv
    #
    cF
    cfv
    #
    clt
    wbr
    #
    vx
    cD
    crab
    #
    cS
    cD
    crest
    co
    #
    wcel
    #
    wph
    @0
    wa
    #
    @4
    cD
    @5
    @7
    @4
    cmnf
    @2
    clt
    wbr
    #
    vx
    cD
    crab
    #
    cD
    @0
    @4
    @9
    wceq
    wph
    @0
    @3
    @8
    vx
    cD
    cA
    cmnf
    @2
    clt
    breq1
    rabbidv
    adantl
    wph
    @9
    cD
    wceq
    @0
    wph
    @9
    cmnf
    vy
    cv
    #
    cF
    cfv
    #
    clt
    wbr
    #
    vy
    cD
    crab
    #
    cD
    cD
    @9
    @13
    wceq
    wph
    @8
    @12
    vx
    vy
    cD
    vx
    cD
    cF
    cdm
    #
    smfpimgtxr.d
    vx
    cF
    smfpimgtxr.x
    nfdm
    nfcxfr
    vy
    cD
    nfcv
    @8
    vy
    nfv
    vx
    cmnf
    @11
    clt
    vx
    cmnf
    nfcv
    vx
    clt
    nfcv
    vx
    @10
    cF
    smfpimgtxr.x
    vx
    @10
    nfcv
    nffv
    nfbr
    @1
    @10
    wceq
    @2
    @11
    cmnf
    clt
    @1
    @10
    cF
    fveq2
    breq2d
    cbvrab
    a1i
    wph
    vy
    cD
    @11
    wph
    vy
    nfv
    wph
    @10
    cD
    wcel
    #
    wa
    cD
    cr
    @10
    cF
    wph
    cD
    cr
    cF
    wf
    @15
    wph
    cD
    cS
    cF
    smfpimgtxr.s
    smfpimgtxr.f
    smfpimgtxr.d
    smff
    #
    adantr
    wph
    @15
    simpr
    ffvelrnd
    pimgtmnf
    wph
    cD
    eqidd
    3eqtrd
    adantr
    eqtrd
    wph
    cD
    @5
    wcel
    @0
    wph
    cD
    @5
    cuni
    #
    @5
    wph
    @17
    cD
    wph
    cS
    cD
    csalg
    smfpimgtxr.s
    wph
    cD
    cS
    cF
    smfpimgtxr.s
    smfpimgtxr.f
    smfpimgtxr.d
    smfdmss
    restuni4
    eqcomd
    wph
    @5
    wph
    cD
    cS
    @5
    cvv
    smfpimgtxr.s
    wph
    cD
    @14
    cvv
    smfpimgtxr.d
    wph
    cF
    cS
    csmblfn
    cfv
    #
    smfpimgtxr.f
    dmexd
    syl5eqel
    @5
    eqid
    subsalsal
    #
    salunid
    eqeltrd
    adantr
    eqeltrd
    wph
    @0
    wn
    #
    cA
    cmnf
    wne
    #
    @6
    @20
    @21
    wph
    cA
    cmnf
    neqne
    adantl
    wph
    @21
    wa
    #
    cA
    cpnf
    wceq
    #
    @6
    wph
    @23
    @6
    @21
    wph
    @23
    wa
    #
    @4
    c0
    @5
    @24
    @4
    cpnf
    @2
    clt
    wbr
    #
    vx
    cD
    crab
    #
    c0
    @23
    @4
    @26
    wceq
    wph
    @23
    @3
    @25
    vx
    cD
    cA
    cpnf
    @2
    clt
    breq1
    rabbidv
    adantl
    wph
    @26
    c0
    wceq
    @23
    wph
    vx
    cD
    cF
    smfpimgtxr.x
    @16
    pimgtpnf2
    adantr
    eqtrd
    wph
    c0
    @5
    wcel
    @23
    wph
    @5
    @19
    0sald
    adantr
    eqeltrd
    adantlr
    @22
    @23
    wn
    #
    wa
    #
    wph
    cA
    cr
    wcel
    #
    @6
    wph
    @21
    @27
    simpll
    #
    @28
    cA
    @28
    wph
    cA
    cxr
    wcel
    @30
    smfpimgtxr.a
    syl
    wph
    @21
    @27
    simplr
    @27
    cA
    cpnf
    wne
    @22
    cA
    cpnf
    neqne
    adantl
    xrred
    wph
    @29
    wa
    vx
    cA
    cD
    cS
    cF
    smfpimgtxr.x
    wph
    cS
    csalg
    wcel
    @29
    smfpimgtxr.s
    adantr
    wph
    cF
    @18
    wcel
    @29
    smfpimgtxr.f
    adantr
    smfpimgtxr.d
    wph
    @29
    simpr
    smfpreimagtf
    syl2anc
    pm2.61dan
    syldan
    pm2.61dan
end
