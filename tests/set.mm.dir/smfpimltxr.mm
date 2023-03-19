include "cpnf.mm"
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
include "breq2.mm"
include "rabbidv.mm"
include "adantl.mm"
include "cuni.mm"
include "wss.mm"
include "cr.mm"
include "wf.mm"
include "wral.mm"
include "csmblfn.mm"
include "w3a.mm"
include "issmff.mm"
include "mpbid.mm"
include "simp2d.mm"
include "pimltpnf2.mm"
include "adantr.mm"
include "eqidd.mm"
include "3eqtrd.mm"
include "csalg.mm"
include "simp1d.mm"
include "restuni4.mm"
include "eqcomd.mm"
include "cvv.mm"
include "cdm.mm"
include "dmexd.mm"
include "syl5eqel.mm"
include "eqid.mm"
include "subsalsal.mm"
include "salunid.mm"
include "eqeltrd.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "cmnf.mm"
include "c0.mm"
include "pimltmnf2.mm"
include "eqtrd.mm"
include "0sald.mm"
include "adantlr.mm"
include "simpll.mm"
include "cxr.mm"
include "syl.mm"
include "simplr.mm"
include "xrred.mm"
include "simpr.mm"
include "smfpreimaltf.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"
include "syldan.mm"

theorem smfpimltxr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vk: setvar k
  assume smfpimltxr.x: |- F/_ x F
  assume smfpimltxr.s: |- ( ph -> S e. SAlg )
  assume smfpimltxr.f: |- ( ph -> F e. ( SMblFn ` S ) )
  assume smfpimltxr.d: |- D = dom F
  assume smfpimltxr.a: |- ( ph -> A e. RR* )

  disjoint A x
  disjoint D x
  disjoint D a
  disjoint a x
  disjoint F a
  disjoint S a
  disjoint k x
  assert |- ( ph -> { x e. D | ( F ` x ) < A } e. ( S |`t D ) )

  proof
    wph
    cA
    cpnf
    wceq
    #
    vx
    cv
    cF
    cfv
    #
    cA
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
    @3
    cD
    @4
    @6
    @3
    @1
    cpnf
    clt
    wbr
    #
    vx
    cD
    crab
    #
    cD
    cD
    @0
    @3
    @8
    wceq
    wph
    @0
    @2
    @7
    vx
    cD
    cA
    cpnf
    @1
    clt
    breq2
    rabbidv
    adantl
    wph
    @8
    cD
    wceq
    @0
    wph
    vx
    cD
    cF
    smfpimltxr.x
    wph
    cD
    cS
    cuni
    wss
    #
    cD
    cr
    cF
    wf
    #
    @1
    va
    cv
    clt
    wbr
    vx
    cD
    crab
    @4
    wcel
    va
    cr
    wral
    #
    wph
    cF
    cS
    csmblfn
    cfv
    #
    wcel
    #
    @9
    @10
    @11
    w3a
    smfpimltxr.f
    wph
    vx
    cD
    cS
    cF
    va
    smfpimltxr.x
    smfpimltxr.s
    smfpimltxr.d
    issmff
    mpbid
    #
    simp2d
    #
    pimltpnf2
    adantr
    @6
    cD
    eqidd
    3eqtrd
    wph
    cD
    @4
    wcel
    @0
    wph
    cD
    @4
    cuni
    #
    @4
    wph
    @16
    cD
    wph
    cS
    cD
    csalg
    smfpimltxr.s
    wph
    @9
    @10
    @11
    @14
    simp1d
    restuni4
    eqcomd
    wph
    @4
    wph
    cD
    cS
    @4
    cvv
    smfpimltxr.s
    wph
    cD
    cF
    cdm
    cvv
    smfpimltxr.d
    wph
    cF
    @12
    smfpimltxr.f
    dmexd
    syl5eqel
    @4
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
    cpnf
    wne
    #
    @5
    @18
    @19
    wph
    cA
    cpnf
    neqne
    adantl
    wph
    @19
    wa
    #
    cA
    cmnf
    wceq
    #
    @5
    wph
    @21
    @5
    @19
    wph
    @21
    wa
    #
    @3
    c0
    @4
    @22
    @3
    @1
    cmnf
    clt
    wbr
    #
    vx
    cD
    crab
    #
    c0
    @21
    @3
    @24
    wceq
    wph
    @21
    @2
    @23
    vx
    cD
    cA
    cmnf
    @1
    clt
    breq2
    rabbidv
    adantl
    @22
    vx
    cD
    cF
    smfpimltxr.x
    wph
    @10
    @21
    @15
    adantr
    pimltmnf2
    eqtrd
    wph
    c0
    @4
    wcel
    @21
    wph
    @4
    @17
    0sald
    adantr
    eqeltrd
    adantlr
    @20
    @21
    wn
    #
    wa
    #
    wph
    cA
    cr
    wcel
    #
    @5
    wph
    @19
    @25
    simpll
    #
    @26
    cA
    @26
    wph
    cA
    cxr
    wcel
    @28
    smfpimltxr.a
    syl
    @25
    cA
    cmnf
    wne
    @20
    cA
    cmnf
    neqne
    adantl
    wph
    @19
    @25
    simplr
    xrred
    wph
    @27
    wa
    vx
    cA
    cD
    cS
    cF
    smfpimltxr.x
    wph
    cS
    csalg
    wcel
    @27
    smfpimltxr.s
    adantr
    wph
    @13
    @27
    smfpimltxr.f
    adantr
    smfpimltxr.d
    wph
    @27
    simpr
    smfpreimaltf
    syl2anc
    pm2.61dan
    syldan
    pm2.61dan
end
