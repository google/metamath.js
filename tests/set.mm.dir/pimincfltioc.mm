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
include "ressiocsup.mm"
include "ssind.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "elinel2.mm"
include "adantl.mm"
include "cxr.mm"
include "wf.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "cle.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "nfv.mm"
include "nfan.mm"
include "cmnf.mm"
include "cioc.mm"
include "co.mm"
include "mnfxr.mm"
include "ressxr.mm"
include "sseldd.mm"
include "elinel1.mm"
include "syl6eleq.mm"
include "iocleub.mm"
include "syl3anc.mm"
include "dmrelrnrel.mm"
include "chvarv.mm"
include "elrab2.mm"
include "sylib.mm"
include "simprd.mm"
include "xrlelttrd.mm"
include "jca.mm"
include "rabeq2i.mm"
include "sylibr.mm"
include "ex.mm"
include "ralrimi.mm"
include "nfci.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "dfss3f.mm"
include "eqssd.mm"

theorem pimincfltioc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cI: class I
  let cY: class Y
  let vz: setvar z
  let vk: setvar k
  assume pimincfltioc.x: |- F/ x ph
  assume pimincfltioc.h: |- F/ y ph
  assume pimincfltioc.a: |- ( ph -> A C_ RR )
  assume pimincfltioc.f: |- ( ph -> F : A --> RR* )
  assume pimincfltioc.i: |- ( ph -> A. x e. A A. y e. A ( x <_ y -> ( F ` x ) <_ ( F ` y ) ) )
  assume pimincfltioc.r: |- ( ph -> R e. RR* )
  assume pimincfltioc.y: |- Y = { x e. A | ( F ` x ) < R }
  assume pimincfltioc.c: |- S = sup ( Y , RR* , < )
  assume pimincfltioc.e: |- ( ph -> S e. Y )
  assume pimincfltioc.d: |- I = ( -oo (,] S )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint I x
  disjoint I y
  disjoint R x
  disjoint S x
  disjoint S y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint I z
  disjoint S z
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
    pimincfltioc.y
    @3
    vx
    cA
    ssrab2
    eqsstri
    #
    a1i
    #
    pimincfltioc.a
    sstrd
    #
    pimincfltioc.c
    pimincfltioc.e
    pimincfltioc.d
    ressiocsup
    @6
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
    @8
    vx
    @0
    pimincfltioc.x
    wph
    @1
    @0
    wcel
    #
    @8
    wph
    @9
    wa
    #
    @1
    cA
    wcel
    #
    @3
    wa
    @8
    @10
    @11
    @3
    @9
    @11
    wph
    @1
    cI
    cA
    elinel2
    adantl
    #
    @10
    @2
    cS
    cF
    cfv
    #
    cR
    @10
    cA
    cxr
    @1
    cF
    wph
    cA
    cxr
    cF
    wf
    @9
    pimincfltioc.f
    adantr
    @12
    ffvelrnd
    wph
    @13
    cxr
    wcel
    @9
    wph
    cA
    cxr
    cS
    cF
    pimincfltioc.f
    wph
    cY
    cA
    cS
    @5
    pimincfltioc.e
    sseldi
    #
    ffvelrnd
    adantr
    wph
    cR
    cxr
    wcel
    @9
    pimincfltioc.r
    adantr
    wph
    vz
    cv
    #
    @0
    wcel
    #
    wa
    #
    @15
    cF
    cfv
    #
    @13
    cle
    wbr
    #
    wi
    @10
    @2
    @13
    cle
    wbr
    #
    wi
    vz
    vx
    @15
    @1
    wceq
    #
    @17
    @10
    @19
    @20
    @21
    @16
    @9
    wph
    @15
    @1
    @0
    eleq1
    anbi2d
    @21
    @18
    @2
    @13
    cle
    @15
    @1
    cF
    fveq2
    breq1d
    imbi12d
    @17
    vx
    vy
    cA
    @15
    cS
    cle
    cle
    cF
    wph
    @16
    vx
    pimincfltioc.x
    @16
    vx
    nfv
    #
    nfan
    wph
    @16
    vy
    pimincfltioc.h
    @16
    vy
    nfv
    nfan
    wph
    @1
    vy
    cv
    #
    cle
    wbr
    @2
    @23
    cF
    cfv
    cle
    wbr
    wi
    vy
    cA
    wral
    vx
    cA
    wral
    @16
    pimincfltioc.i
    adantr
    @16
    @15
    cA
    wcel
    wph
    @15
    cI
    cA
    elinel2
    adantl
    wph
    cS
    cA
    wcel
    #
    @16
    @14
    adantr
    @17
    cmnf
    cxr
    wcel
    #
    cS
    cxr
    wcel
    #
    @15
    cmnf
    cS
    cioc
    co
    #
    wcel
    #
    @15
    cS
    cle
    wbr
    @25
    @17
    mnfxr
    a1i
    wph
    @26
    @16
    wph
    cr
    cxr
    cS
    ressxr
    wph
    cY
    cr
    cS
    @7
    pimincfltioc.e
    sseldd
    sseldi
    adantr
    @16
    @28
    wph
    @16
    @15
    cI
    @27
    @15
    cI
    cA
    elinel1
    pimincfltioc.d
    syl6eleq
    adantl
    cmnf
    cS
    @15
    iocleub
    syl3anc
    dmrelrnrel
    chvarv
    wph
    @13
    cR
    clt
    wbr
    #
    @9
    wph
    @24
    @29
    wph
    cS
    cY
    wcel
    @24
    @29
    wa
    pimincfltioc.e
    @3
    @29
    vx
    cS
    cA
    cY
    @1
    cS
    wceq
    @2
    @13
    cR
    clt
    @1
    cS
    cF
    fveq2
    breq1d
    pimincfltioc.y
    elrab2
    sylib
    simprd
    adantr
    xrlelttrd
    jca
    @3
    vx
    cY
    cA
    pimincfltioc.y
    rabeq2i
    sylibr
    ex
    ralrimi
    vx
    @0
    cY
    vx
    vz
    @0
    @22
    nfci
    vx
    cY
    @4
    pimincfltioc.y
    @3
    vx
    cA
    nfrab1
    nfcxfr
    dfss3f
    sylibr
    eqssd
end
