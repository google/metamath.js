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
include "breq2d.mm"
include "elrab2.mm"
include "biimpi.mm"
include "simprd.mm"
include "ad2antlr.mm"
include "sseldd.mm"
include "ad2antrr.mm"
include "sselda.mm"
include "ad4ant13.mm"
include "ltnled.mm"
include "ltled.mm"
include "adantllr.mm"
include "ad5ant14.mm"
include "ad3antrrr.mm"
include "wi.mm"
include "rspa.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "mpd.mm"
include "simpllr.mm"
include "xrletrd.mm"
include "mpbid.mm"
include "syldan.mm"
include "condan.mm"
include "ex.mm"
include "ralrimi.mm"
include "wb.mm"
include "sseldi.mm"
include "supxrleub.mm"
include "syl5eqbr.mm"
include "jca.mm"
include "rabeq2i.mm"
include "sylibr.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "dfss3f.mm"
include "eqssd.mm"

theorem pimdecfgtioo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cI: class I
  let cY: class Y
  let vk: setvar k
  assume pimdecfgtioo.x: |- F/ x ph
  assume pimdecfgtioo.h: |- F/ y ph
  assume pimdecfgtioo.a: |- ( ph -> A C_ RR )
  assume pimdecfgtioo.f: |- ( ph -> F : A --> RR* )
  assume pimdecfgtioo.d: |- ( ph -> A. x e. A A. y e. A ( x <_ y -> ( F ` y ) <_ ( F ` x ) ) )
  assume pimdecfgtioo.r: |- ( ph -> R e. RR* )
  assume pimdecfgtioo.y: |- Y = { x e. A | R < ( F ` x ) }
  assume pimdecfgtioo.c: |- S = sup ( Y , RR* , < )
  assume pimdecfgtioo.e: |- ( ph -> -. S e. Y )
  assume pimdecfgtioo.i: |- I = ( -oo (,) S )

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
    cR
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
    cA
    crab
    #
    cA
    pimdecfgtioo.y
    @3
    vx
    cA
    ssrab2
    eqsstri
    a1i
    #
    pimdecfgtioo.a
    sstrd
    #
    pimdecfgtioo.c
    pimdecfgtioo.e
    pimdecfgtioo.i
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
    pimdecfgtioo.x
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
    #
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
    @13
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
    @13
    @15
    @9
    mnfxr
    a1i
    wph
    @16
    @8
    wph
    cS
    cY
    cxr
    clt
    csup
    #
    cxr
    pimdecfgtioo.c
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
    @18
    wph
    @8
    @1
    cI
    @17
    @1
    cI
    cA
    elinel1
    pimdecfgtioo.i
    syl6eleq
    adantl
    cmnf
    cS
    @1
    iooltub
    syl3anc
    adantr
    @9
    @14
    wa
    #
    cS
    @1
    cle
    wbr
    @13
    wn
    @22
    cS
    @19
    @1
    cle
    pimdecfgtioo.c
    @22
    @19
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
    @14
    @2
    cR
    cle
    wbr
    #
    @26
    @22
    @27
    @14
    @9
    @14
    simpr
    @22
    @2
    cR
    @9
    @2
    cxr
    wcel
    #
    @14
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
    pimdecfgtioo.f
    adantr
    @12
    ffvelrnd
    #
    adantr
    @9
    cR
    cxr
    wcel
    #
    @14
    wph
    @31
    @8
    pimdecfgtioo.r
    adantr
    #
    adantr
    xrlenltd
    mpbird
    @9
    @27
    wa
    #
    @25
    vy
    cY
    @9
    @27
    vy
    wph
    @8
    vy
    pimdecfgtioo.h
    @8
    vy
    nfv
    nfan
    @27
    vy
    nfv
    nfan
    @33
    @24
    cY
    wcel
    #
    @25
    @33
    @34
    wa
    #
    @25
    cR
    @24
    cF
    cfv
    #
    clt
    wbr
    #
    @34
    @37
    @33
    @25
    wn
    #
    @34
    @24
    cA
    wcel
    #
    @37
    @34
    @39
    @37
    wa
    @3
    @37
    vx
    @24
    cA
    cY
    @1
    @24
    wceq
    @2
    @36
    cR
    clt
    @1
    @24
    cF
    fveq2
    breq2d
    pimdecfgtioo.y
    elrab2
    biimpi
    simprd
    ad2antlr
    @35
    @38
    @1
    @24
    cle
    wbr
    #
    @37
    wn
    #
    @9
    @34
    @38
    @40
    @27
    @9
    @34
    wa
    #
    @38
    wa
    #
    @1
    @24
    @9
    @1
    cr
    wcel
    @34
    @38
    @9
    cA
    cr
    @1
    wph
    cA
    cr
    wss
    @8
    pimdecfgtioo.a
    adantr
    @12
    sseldd
    #
    ad2antrr
    #
    wph
    @34
    @24
    cr
    wcel
    @8
    @38
    wph
    cY
    cr
    @24
    @6
    sselda
    ad4ant13
    #
    @43
    @1
    @24
    clt
    wbr
    @38
    @42
    @38
    simpr
    @43
    @1
    @24
    @45
    @46
    ltnled
    mpbird
    ltled
    adantllr
    @35
    @40
    wa
    #
    @36
    cR
    cle
    wbr
    @41
    @47
    @36
    @2
    cR
    wph
    @34
    @36
    cxr
    wcel
    @8
    @27
    @40
    wph
    @34
    wa
    cA
    cxr
    @24
    cF
    wph
    @29
    @34
    pimdecfgtioo.f
    adantr
    wph
    cY
    cA
    @24
    @5
    sselda
    #
    ffvelrnd
    ad5ant14
    #
    @9
    @28
    @27
    @34
    @40
    @30
    ad3antrrr
    @9
    @31
    @27
    @34
    @40
    @32
    ad3antrrr
    #
    @9
    @34
    @40
    @36
    @2
    cle
    wbr
    #
    @27
    @42
    @40
    wa
    #
    @40
    @51
    @42
    @40
    simpr
    @52
    @40
    @51
    wi
    #
    vy
    cA
    wral
    #
    @39
    @53
    @9
    @54
    @34
    @40
    wph
    @54
    vx
    cA
    wral
    @10
    @54
    @8
    pimdecfgtioo.d
    @11
    @54
    vx
    cA
    rspa
    syl2an
    ad2antrr
    wph
    @34
    @39
    @8
    @40
    @48
    ad4ant13
    @53
    vy
    cA
    rspa
    syl2anc
    mpd
    adantllr
    @9
    @27
    @34
    @40
    simpllr
    xrletrd
    @47
    @36
    cR
    @49
    @50
    xrlenltd
    mpbid
    syldan
    condan
    ex
    ralrimi
    syldan
    @9
    @23
    @26
    wb
    #
    @14
    @9
    cY
    cxr
    wss
    #
    @1
    cxr
    wcel
    #
    @55
    wph
    @56
    @8
    @20
    adantr
    @9
    cr
    cxr
    @1
    ressxr
    @44
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
    @22
    cS
    @1
    @9
    @16
    @14
    @21
    adantr
    @9
    @57
    @14
    @58
    adantr
    xrlenltd
    mpbid
    condan
    jca
    @3
    vx
    cY
    cA
    pimdecfgtioo.y
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
    pimdecfgtioo.y
    @3
    vx
    cA
    nfrab1
    nfcxfr
    dfss3f
    sylibr
    eqssd
end
