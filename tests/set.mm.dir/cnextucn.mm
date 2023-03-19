include "cuni.mm"
include "eqid.mm"
include "ctps.mm"
include "wcel.mm"
include "ctop.mm"
include "tpstop.mm"
include "syl.mm"
include "wf.mm"
include "wceq.mm"
include "tpsuni.mm"
include "feq3d.mm"
include "mpbid.mm"
include "sseqtrd.mm"
include "ccl.mm"
include "cfv.mm"
include "eqtrd.mm"
include "cv.mm"
include "wa.mm"
include "csn.mm"
include "cnei.mm"
include "crest.mm"
include "co.mm"
include "cflf.mm"
include "cfm.mm"
include "cflim.mm"
include "c0.mm"
include "ctopon.mm"
include "cfil.mm"
include "istps.mm"
include "sylib.mm"
include "adantr.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "eleqtrrd.mm"
include "wss.mm"
include "wb.mm"
include "toptopon.mm"
include "fveq2.mm"
include "mpbird.mm"
include "trnei.mm"
include "syl3anc.mm"
include "flfval.mm"
include "ccusp.mm"
include "cuss.mm"
include "ccfilu.mm"
include "wne.mm"
include "syldan.mm"
include "fveq2i.mm"
include "syl6eleq.mm"
include "cvv.mm"
include "cfbas.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "filfbas.mm"
include "fmfil.mm"
include "cuspcvg.mm"
include "eqnetrd.mm"
include "cusp.mm"
include "cha.mm"
include "creg.mm"
include "cuspusp.mm"
include "uspreg.mm"
include "syl2anc.mm"
include "cnextcn.mm"

theorem cnextucn
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cU: class U
  let cF: class F
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume cnextucn.x: |- X = ( Base ` V )
  assume cnextucn.y: |- Y = ( Base ` W )
  assume cnextucn.j: |- J = ( TopOpen ` V )
  assume cnextucn.k: |- K = ( TopOpen ` W )
  assume cnextucn.u: |- U = ( UnifSt ` W )
  assume cnextucn.v: |- ( ph -> V e. TopSp )
  assume cnextucn.t: |- ( ph -> W e. TopSp )
  assume cnextucn.w: |- ( ph -> W e. CUnifSp )
  assume cnextucn.h: |- ( ph -> K e. Haus )
  assume cnextucn.a: |- ( ph -> A C_ X )
  assume cnextucn.f: |- ( ph -> F : A --> Y )
  assume cnextucn.c: |- ( ph -> ( ( cls ` J ) ` A ) = X )
  assume cnextucn.l: |- ( ( ph /\ x e. X ) -> ( ( Y FilMap F ) ` ( ( ( nei ` J ) ` { x } ) |`t A ) ) e. ( CauFilU ` U ) )

  disjoint A x
  disjoint F x
  disjoint J x
  disjoint K x
  disjoint ph x
  assert |- ( ph -> ( ( J CnExt K ) ` F ) e. ( J Cn K ) )

  proof
    wph
    vx
    cA
    cK
    cuni
    #
    cJ
    cuni
    #
    cF
    cJ
    cK
    @1
    eqid
    #
    @0
    eqid
    wph
    cV
    ctps
    wcel
    #
    cJ
    ctop
    wcel
    #
    cnextucn.v
    cJ
    cV
    cnextucn.j
    tpstop
    syl
    #
    cnextucn.h
    wph
    cA
    cY
    cF
    wf
    #
    cA
    @0
    cF
    wf
    cnextucn.f
    wph
    cY
    @0
    cF
    cA
    wph
    cW
    ctps
    wcel
    #
    cY
    @0
    wceq
    cnextucn.t
    cY
    cK
    cW
    cnextucn.y
    cnextucn.k
    tpsuni
    syl
    feq3d
    mpbid
    wph
    cA
    cX
    @1
    cnextucn.a
    wph
    @3
    cX
    @1
    wceq
    #
    cnextucn.v
    cX
    cJ
    cV
    cnextucn.x
    cnextucn.j
    tpsuni
    syl
    #
    sseqtrd
    wph
    cA
    cJ
    ccl
    cfv
    cfv
    #
    cX
    @1
    cnextucn.c
    @9
    eqtrd
    wph
    vx
    cv
    #
    @1
    wcel
    #
    wa
    #
    cF
    cK
    @11
    csn
    cJ
    cnei
    cfv
    cfv
    cA
    crest
    co
    #
    cflf
    co
    cfv
    #
    cK
    @14
    cY
    cF
    cfm
    co
    cfv
    #
    cflim
    co
    #
    c0
    @13
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @14
    cA
    cfil
    cfv
    wcel
    #
    @6
    @15
    @17
    wceq
    wph
    @18
    @12
    wph
    @7
    @18
    cnextucn.t
    cY
    cK
    cW
    cnextucn.y
    cnextucn.k
    istps
    sylib
    adantr
    @13
    @11
    @10
    wcel
    #
    @19
    @13
    @11
    cX
    @10
    wph
    @11
    cX
    wcel
    #
    @12
    wph
    cX
    @1
    @11
    @9
    eleq2d
    biimpar
    #
    wph
    @10
    cX
    wceq
    @12
    cnextucn.c
    adantr
    eleqtrrd
    @13
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cA
    cX
    wss
    #
    @21
    @20
    @19
    wb
    wph
    @24
    @12
    wph
    @24
    cJ
    @1
    ctopon
    cfv
    #
    wcel
    #
    wph
    @4
    @27
    @5
    cJ
    @1
    @2
    toptopon
    sylib
    wph
    @8
    @24
    @27
    wb
    @9
    @8
    @23
    @26
    cJ
    cX
    @1
    ctopon
    fveq2
    eleq2d
    syl
    mpbird
    adantr
    wph
    @25
    @12
    cnextucn.a
    adantr
    @22
    cA
    @11
    cJ
    cX
    trnei
    syl3anc
    mpbid
    #
    wph
    @6
    @12
    cnextucn.f
    adantr
    #
    cF
    cK
    @14
    cY
    cA
    flfval
    syl3anc
    @13
    cW
    ccusp
    wcel
    #
    @16
    cW
    cuss
    cfv
    #
    ccfilu
    cfv
    #
    wcel
    @16
    cY
    cfil
    cfv
    wcel
    #
    @17
    c0
    wne
    wph
    @30
    @12
    cnextucn.w
    adantr
    @13
    @16
    cU
    ccfilu
    cfv
    #
    @32
    wph
    @12
    @21
    @16
    @34
    wcel
    @22
    cnextucn.l
    syldan
    cU
    @31
    ccfilu
    cnextucn.u
    fveq2i
    syl6eleq
    @13
    cY
    cvv
    wcel
    #
    @14
    cA
    cfbas
    cfv
    wcel
    #
    @6
    @33
    @35
    @13
    cY
    cW
    cbs
    cfv
    cvv
    cnextucn.y
    cW
    cbs
    fvex
    eqeltri
    a1i
    @13
    @19
    @36
    @28
    @14
    cA
    filfbas
    syl
    @29
    cvv
    @14
    cF
    cY
    cA
    fmfil
    syl3anc
    cY
    @16
    cK
    cW
    cnextucn.y
    cnextucn.k
    cuspcvg
    syl3anc
    eqnetrd
    wph
    cW
    cusp
    wcel
    #
    cK
    cha
    wcel
    cK
    creg
    wcel
    wph
    @30
    @37
    cnextucn.w
    cW
    cuspusp
    syl
    cnextucn.h
    cK
    cW
    cnextucn.k
    uspreg
    syl2anc
    cnextcn
end
