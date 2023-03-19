include "csn.mm"
include "cun.mm"
include "cprod.mm"
include "cmpt.mm"
include "csb.mm"
include "cmul.mm"
include "co.mm"
include "ccn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cdif.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcsb1v.mm"
include "cfn.mm"
include "ssfid.mm"
include "adantr.mm"
include "eldifbd.mm"
include "cc.mm"
include "sselda.mm"
include "adantlr.mm"
include "wral.mm"
include "wf.mm"
include "ctopon.mm"
include "cfv.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "simplr.mm"
include "rspa.mm"
include "syl2anc.mm"
include "syldan.mm"
include "csbeq1a.mm"
include "eldifad.mm"
include "simpr.mm"
include "wi.mm"
include "nfcv.mm"
include "nfel1.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtoclgf.mm"
include "mpcom.mm"
include "mpdan.mm"
include "fprodsplitsn.mm"
include "mpteq2dva.mm"
include "nfmpt.mm"
include "nfel.mm"
include "mpteq2dv.mm"
include "idi.mm"
include "anabsi7.mm"
include "ctx.mm"
include "mulcn.mm"
include "cnmpt12f.mm"
include "eqeltrd.mm"

theorem fprodcnlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cJ: class J
  let cK: class K
  let cW: class W
  let cX: class X
  let cZ: class Z
  assume fprodcnlem.1: |- F/ k ph
  assume fprodcnlem.k: |- K = ( TopOpen ` CCfld )
  assume fprodcnlem.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume fprodcnlem.a: |- ( ph -> A e. Fin )
  assume fprodcnlem.b: |- ( ( ph /\ k e. A ) -> ( x e. X |-> B ) e. ( J Cn K ) )
  assume fprodcnlem.z: |- ( ph -> Z C_ A )
  assume fprodcnlem.w: |- ( ph -> W e. ( A \ Z ) )
  assume fprodcnlem.p: |- ( ph -> ( x e. X |-> prod_ k e. Z B ) e. ( J Cn K ) )

  disjoint A k
  disjoint J k
  disjoint J x
  disjoint k x
  disjoint K k
  disjoint K x
  disjoint W k
  disjoint W x
  disjoint X k
  disjoint X x
  disjoint Z k
  disjoint ph x
  assert |- ( ph -> ( x e. X |-> prod_ k e. ( Z u. { W } ) B ) e. ( J Cn K ) )

  proof
    wph
    vx
    cX
    cZ
    cW
    csn
    cun
    cB
    vk
    cprod
    #
    cmpt
    vx
    cX
    cZ
    cB
    vk
    cprod
    #
    vk
    cW
    cB
    csb
    #
    cmul
    co
    #
    cmpt
    cJ
    cK
    ccn
    co
    #
    wph
    vx
    cX
    @0
    @3
    wph
    vx
    cv
    cX
    wcel
    #
    wa
    #
    cZ
    cW
    cB
    @2
    vk
    cA
    cZ
    cdif
    #
    wph
    @5
    vk
    fprodcnlem.1
    @5
    vk
    nfv
    nfan
    #
    vk
    cW
    cB
    nfcsb1v
    #
    wph
    cZ
    cfn
    wcel
    @5
    wph
    cA
    cZ
    fprodcnlem.a
    fprodcnlem.z
    ssfid
    adantr
    wph
    cW
    @7
    wcel
    @5
    fprodcnlem.w
    adantr
    #
    @6
    cW
    cA
    cZ
    @10
    eldifbd
    @6
    vk
    cv
    #
    cZ
    wcel
    #
    @11
    cA
    wcel
    #
    cB
    cc
    wcel
    #
    wph
    @12
    @13
    @5
    wph
    cZ
    cA
    @11
    fprodcnlem.z
    sselda
    adantlr
    @6
    @13
    wa
    #
    @14
    vx
    cX
    wral
    #
    @5
    @14
    wph
    @13
    @16
    @5
    wph
    @13
    wa
    #
    cX
    cc
    vx
    cX
    cB
    cmpt
    #
    wf
    #
    @16
    @17
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cc
    ctopon
    cfv
    wcel
    #
    @18
    @4
    wcel
    #
    @19
    wph
    @20
    @13
    fprodcnlem.j
    adantr
    @21
    @17
    cK
    fprodcnlem.k
    cnfldtopon
    a1i
    fprodcnlem.b
    @18
    cJ
    cK
    cX
    cc
    cnf2
    syl3anc
    vx
    cX
    cc
    cB
    @18
    @18
    eqid
    fmpt
    sylibr
    adantlr
    wph
    @5
    @13
    simplr
    @14
    vx
    cX
    rspa
    syl2anc
    #
    syldan
    vk
    cW
    cB
    csbeq1a
    #
    @6
    cW
    cA
    wcel
    #
    @2
    cc
    wcel
    #
    @6
    cW
    cA
    cZ
    @10
    eldifad
    @25
    @6
    @25
    wa
    #
    @26
    @6
    @25
    simpr
    @15
    @14
    wi
    @27
    @26
    wi
    vk
    cW
    cA
    vk
    cW
    nfcv
    #
    @27
    @26
    vk
    @6
    @25
    vk
    @8
    @25
    vk
    nfv
    #
    nfan
    vk
    @2
    cc
    @9
    nfel1
    nfim
    @11
    cW
    wceq
    #
    @15
    @27
    @14
    @26
    @30
    @13
    @25
    @6
    @11
    cW
    cA
    eleq1
    #
    anbi2d
    @30
    cB
    @2
    cc
    @24
    eleq1d
    imbi12d
    @23
    vtoclgf
    mpcom
    mpdan
    fprodsplitsn
    mpteq2dva
    wph
    vx
    @1
    @2
    cmul
    cJ
    cK
    cK
    cK
    cX
    fprodcnlem.j
    fprodcnlem.p
    wph
    @25
    vx
    cX
    @2
    cmpt
    #
    @4
    wcel
    #
    wph
    cW
    cA
    cZ
    fprodcnlem.w
    eldifad
    wph
    @25
    @33
    @17
    @22
    wi
    #
    wph
    @25
    wa
    #
    @33
    wi
    vk
    cW
    cA
    @28
    @35
    @33
    vk
    wph
    @25
    vk
    fprodcnlem.1
    @29
    nfan
    vk
    @32
    @4
    vk
    vx
    cX
    @2
    vk
    cX
    nfcv
    @9
    nfmpt
    vk
    @4
    nfcv
    nfel
    nfim
    @30
    @17
    @35
    @22
    @33
    @30
    @13
    @25
    wph
    @31
    anbi2d
    @30
    @18
    @32
    @4
    @30
    vx
    cX
    cB
    @2
    @24
    mpteq2dv
    eleq1d
    imbi12d
    @34
    fprodcnlem.b
    idi
    vtoclgf
    anabsi7
    mpdan
    cmul
    cK
    cK
    ctx
    co
    cK
    ccn
    co
    wcel
    wph
    cK
    fprodcnlem.k
    mulcn
    a1i
    cnmpt12f
    eqeltrd
end
