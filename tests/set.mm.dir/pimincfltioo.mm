include "cin.mm"
include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "sstrd.mm"
include "ressioosup.mm"
include "ssind.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "elinel2.mm"
include "adantl.mm"
include "wn.mm"
include "cmnf.mm"
include "cxr.mm"
include "cioo.mm"
include "co.mm"
include "mnfxr.mm"
include "csup.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrcld.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "elinel1.mm"
include "syl6eleq.mm"
include "iooltub.mm"
include "syl3anc.mm"
include "cle.mm"
include "simpr.mm"
include "wf.mm"
include "ffvelrnd.mm"
include "xrlenltd.mm"
include "mpbird.mm"
include "nfv.mm"
include "nfan.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab2.mm"
include "biimpi.mm"
include "simprd.mm"
include "ad5ant14.mm"
include "sseldd.mm"
include "ad3antrrr.mm"
include "sselda.mm"
include "ad2antrr.mm"
include "ad4ant13.mm"
include "ltnled.mm"
include "adantllr.mm"
include "ltled.mm"
include "simpllr.mm"
include "wi.mm"
include "breq1.mm"
include "imbi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "cbvral2v.mm"
include "sylibr.mm"
include "dmrelrnrel.mm"
include "xrletrd.mm"
include "mpbid.mm"
include "syldan.mm"
include "condan.mm"
include "ex.mm"
include "ralrimi.mm"
include "wb.mm"
include "sseldi.mm"
include "supxrleub.mm"
include "syl2anc.mm"
include "syl5eqbr.mm"
include "jca.mm"
include "rabeq2i.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "dfss3f.mm"
include "eqssd.mm"

theorem pimincfltioo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cI: class I
  let cY: class Y
  let vw: setvar w
  let vz: setvar z
  let vk: setvar k
  assume pimincfltioo.x: |- F/ x ph
  assume pimincfltioo.h: |- F/ y ph
  assume pimincfltioo.a: |- ( ph -> A C_ RR )
  assume pimincfltioo.f: |- ( ph -> F : A --> RR* )
  assume pimincfltioo.i: |- ( ph -> A. x e. A A. y e. A ( x <_ y -> ( F ` x ) <_ ( F ` y ) ) )
  assume pimincfltioo.r: |- ( ph -> R e. RR* )
  assume pimincfltioo.y: |- Y = { x e. A | ( F ` x ) < R }
  assume pimincfltioo.c: |- S = sup ( Y , RR* , < )
  assume pimincfltioo.e: |- ( ph -> -. S e. Y )
  assume pimincfltioo.d: |- I = ( -oo (,) S )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint I x
  disjoint I y
  disjoint R x
  disjoint R y
  disjoint Y y
  disjoint A w
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint F w
  disjoint F z
  disjoint I w
  disjoint I z
  disjoint Y w
  disjoint Y z
  disjoint ph w
  disjoint ph z
  disjoint k x
  assert |- ( ph -> Y = ( I i^i A ) )

  proof
    wph
    cY
    cI
    cA
    cin
    #
    wph
    cY
    cI
    cA
    wph
    cY
    cS
    cI
    wph
    cY
    cA
    cr
    cY
    cA
    wss
    wph
    cY
    vx
    cv
    #
    cF
    cfv
    #
    cR
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cA
    pimincfltioo.y
    @3
    vx
    cA
    ssrab2
    eqsstri
    a1i
    #
    pimincfltioo.a
    sstrd
    #
    pimincfltioo.c
    pimincfltioo.e
    pimincfltioo.d
    ressioosup
    @5
    ssind
    wph
    @1
    cY
    wcel
    #
    vx
    @0
    wral
    @0
    cY
    wss
    wph
    @7
    vx
    @0
    pimincfltioo.x
    wph
    @1
    @0
    wcel
    #
    @7
    wph
    @8
    wa
    #
    @1
    cA
    wcel
    #
    @3
    wa
    @7
    @9
    @10
    @3
    @8
    @10
    wph
    @1
    cI
    cA
    elinel2
    adantl
    #
    @9
    @3
    @1
    cS
    clt
    wbr
    #
    @9
    @12
    @3
    wn
    #
    @9
    cmnf
    cxr
    wcel
    #
    cS
    cxr
    wcel
    #
    @1
    cmnf
    cS
    cioo
    co
    #
    wcel
    #
    @12
    @14
    @9
    mnfxr
    a1i
    wph
    @15
    @8
    wph
    cS
    cY
    cxr
    clt
    csup
    #
    cxr
    pimincfltioo.c
    wph
    cY
    wph
    cY
    cr
    cxr
    @6
    ressxr
    syl6ss
    #
    supxrcld
    syl5eqel
    adantr
    #
    @8
    @17
    wph
    @8
    @1
    cI
    @16
    @1
    cI
    cA
    elinel1
    pimincfltioo.d
    syl6eleq
    adantl
    cmnf
    cS
    @1
    iooltub
    syl3anc
    adantr
    @9
    @13
    wa
    #
    cS
    @1
    cle
    wbr
    @12
    wn
    @21
    cS
    @18
    @1
    cle
    pimincfltioo.c
    @21
    @18
    @1
    cle
    wbr
    #
    vy
    cv
    #
    @1
    cle
    wbr
    #
    vy
    cY
    wral
    #
    @9
    @13
    cR
    @2
    cle
    wbr
    #
    @25
    @21
    @26
    @13
    @9
    @13
    simpr
    @21
    cR
    @2
    @9
    cR
    cxr
    wcel
    #
    @13
    wph
    @27
    @8
    pimincfltioo.r
    adantr
    #
    adantr
    @9
    @2
    cxr
    wcel
    #
    @13
    @9
    cA
    cxr
    @1
    cF
    wph
    cA
    cxr
    cF
    wf
    #
    @8
    pimincfltioo.f
    adantr
    @11
    ffvelrnd
    #
    adantr
    xrlenltd
    mpbird
    @9
    @26
    wa
    #
    @24
    vy
    cY
    @9
    @26
    vy
    wph
    @8
    vy
    pimincfltioo.h
    @8
    vy
    nfv
    nfan
    @26
    vy
    nfv
    nfan
    @32
    @23
    cY
    wcel
    #
    @24
    @32
    @33
    wa
    #
    @24
    @23
    cF
    cfv
    #
    cR
    clt
    wbr
    #
    wph
    @33
    @36
    @8
    @26
    @24
    wn
    #
    @33
    @36
    wph
    @33
    @23
    cA
    wcel
    #
    @36
    @33
    @38
    @36
    wa
    @3
    @36
    vx
    @23
    cA
    cY
    @1
    @23
    wceq
    @2
    @35
    cR
    clt
    @1
    @23
    cF
    fveq2
    breq1d
    pimincfltioo.y
    elrab2
    biimpi
    simprd
    adantl
    ad5ant14
    @34
    @37
    @1
    @23
    cle
    wbr
    #
    @36
    wn
    #
    @34
    @37
    wa
    @1
    @23
    @9
    @1
    cr
    wcel
    #
    @26
    @33
    @37
    @9
    cA
    cr
    @1
    wph
    cA
    cr
    wss
    @8
    pimincfltioo.a
    adantr
    @11
    sseldd
    #
    ad3antrrr
    wph
    @33
    @23
    cr
    wcel
    #
    @8
    @26
    @37
    wph
    cY
    cr
    @23
    @6
    sselda
    #
    ad5ant14
    @9
    @33
    @37
    @1
    @23
    clt
    wbr
    #
    @26
    @9
    @33
    wa
    #
    @37
    wa
    #
    @45
    @37
    @46
    @37
    simpr
    @47
    @1
    @23
    @9
    @41
    @33
    @37
    @42
    ad2antrr
    wph
    @33
    @43
    @8
    @37
    @44
    ad4ant13
    ltnled
    mpbird
    adantllr
    ltled
    @34
    @39
    wa
    #
    cR
    @35
    cle
    wbr
    @40
    @48
    cR
    @2
    @35
    @9
    @27
    @26
    @33
    @39
    @28
    ad3antrrr
    #
    @9
    @29
    @26
    @33
    @39
    @31
    ad3antrrr
    wph
    @33
    @35
    cxr
    wcel
    @8
    @26
    @39
    wph
    @33
    wa
    cA
    cxr
    @23
    cF
    wph
    @30
    @33
    pimincfltioo.f
    adantr
    wph
    cY
    cA
    @23
    @5
    sselda
    #
    ffvelrnd
    ad5ant14
    #
    @9
    @26
    @33
    @39
    simpllr
    @9
    @33
    @39
    @2
    @35
    cle
    wbr
    #
    @26
    @46
    @39
    wa
    #
    vw
    vz
    cA
    @1
    @23
    cle
    cle
    cF
    @53
    vw
    nfv
    @53
    vz
    nfv
    wph
    vw
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    @54
    cF
    cfv
    #
    @55
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vz
    cA
    wral
    vw
    cA
    wral
    #
    @8
    @33
    @39
    wph
    @39
    @52
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    @61
    pimincfltioo.i
    @60
    @62
    @1
    @55
    cle
    wbr
    #
    @2
    @58
    cle
    wbr
    #
    wi
    vw
    vz
    vx
    vy
    cA
    cA
    @54
    @1
    wceq
    #
    @56
    @63
    @59
    @64
    @54
    @1
    @55
    cle
    breq1
    @65
    @57
    @2
    @58
    cle
    @54
    @1
    cF
    fveq2
    breq1d
    imbi12d
    @55
    @23
    wceq
    #
    @63
    @39
    @64
    @52
    @55
    @23
    @1
    cle
    breq2
    @66
    @58
    @35
    @2
    cle
    @55
    @23
    cF
    fveq2
    breq2d
    imbi12d
    cbvral2v
    sylibr
    ad3antrrr
    @9
    @10
    @33
    @39
    @11
    ad2antrr
    wph
    @33
    @38
    @8
    @39
    @50
    ad4ant13
    @46
    @39
    simpr
    dmrelrnrel
    adantllr
    xrletrd
    @48
    cR
    @35
    @49
    @51
    xrlenltd
    mpbid
    syldan
    condan
    ex
    ralrimi
    syldan
    @9
    @22
    @25
    wb
    #
    @13
    @9
    cY
    cxr
    wss
    #
    @1
    cxr
    wcel
    #
    @67
    wph
    @68
    @8
    @19
    adantr
    @9
    cr
    cxr
    @1
    ressxr
    @42
    sseldi
    #
    vy
    cY
    @1
    supxrleub
    syl2anc
    adantr
    mpbird
    syl5eqbr
    @21
    cS
    @1
    @9
    @15
    @13
    @20
    adantr
    @9
    @69
    @13
    @70
    adantr
    xrlenltd
    mpbid
    condan
    jca
    @3
    vx
    cY
    cA
    pimincfltioo.y
    rabeq2i
    sylibr
    ex
    ralrimi
    vx
    @0
    cY
    vx
    @0
    nfcv
    vx
    cY
    @4
    pimincfltioo.y
    @3
    vx
    cA
    nfrab1
    nfcxfr
    dfss3f
    sylibr
    eqssd
end
