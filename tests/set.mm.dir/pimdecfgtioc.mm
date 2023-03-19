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
include "adantr.mm"
include "sseldi.mm"
include "ffvelrnd.mm"
include "wf.mm"
include "syl6eleq.mm"
include "csup.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nfsup.mm"
include "nffv.mm"
include "nfbr.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "elrabf.mm"
include "sylib.mm"
include "simprd.mm"
include "cle.mm"
include "wi.mm"
include "r19.21bi.mm"
include "syldan.mm"
include "jca.mm"
include "cmnf.mm"
include "cioc.mm"
include "co.mm"
include "mnfxr.mm"
include "ressxr.mm"
include "sseldd.mm"
include "elinel1.mm"
include "iocleub.mm"
include "syl3anc.mm"
include "breq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "sylc.mm"
include "xrltletrd.mm"
include "rabeq2i.mm"
include "sylibr.mm"
include "ex.mm"
include "ralrimi.mm"
include "nfv.mm"
include "nfci.mm"
include "dfss3f.mm"
include "eqssd.mm"

theorem pimdecfgtioc
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
  assume pimdecfgtioc.x: |- F/ x ph
  assume pimdecfgtioc.a: |- ( ph -> A C_ RR )
  assume pimdecfgtioc.f: |- ( ph -> F : A --> RR* )
  assume pimdecfgtioc.i: |- ( ph -> A. x e. A A. y e. A ( x <_ y -> ( F ` y ) <_ ( F ` x ) ) )
  assume pimdecfgtioc.r: |- ( ph -> R e. RR* )
  assume pimdecfgtioc.y: |- Y = { x e. A | R < ( F ` x ) }
  assume pimdecfgtioc.c: |- S = sup ( Y , RR* , < )
  assume pimdecfgtioc.e: |- ( ph -> S e. Y )
  assume pimdecfgtioc.d: |- I = ( -oo (,] S )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint I x
  disjoint R x
  disjoint S y
  disjoint A z
  disjoint x z
  disjoint I z
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
    pimdecfgtioc.y
    @3
    vx
    cA
    ssrab2
    eqsstri
    #
    a1i
    #
    pimdecfgtioc.a
    sstrd
    #
    pimdecfgtioc.c
    pimdecfgtioc.e
    pimdecfgtioc.d
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
    pimdecfgtioc.x
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
    cR
    cS
    cF
    cfv
    #
    @2
    wph
    cR
    cxr
    wcel
    @9
    pimdecfgtioc.r
    adantr
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
    pimdecfgtioc.f
    wph
    cY
    cA
    cS
    @5
    pimdecfgtioc.e
    sseldi
    #
    ffvelrnd
    adantr
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
    pimdecfgtioc.f
    adantr
    @12
    ffvelrnd
    wph
    cR
    @13
    clt
    wbr
    #
    @9
    wph
    cS
    cA
    wcel
    #
    @15
    wph
    cS
    @4
    wcel
    @16
    @15
    wa
    wph
    cS
    cY
    @4
    pimdecfgtioc.e
    pimdecfgtioc.y
    syl6eleq
    @3
    @15
    vx
    cS
    cA
    vx
    cS
    cY
    cxr
    clt
    csup
    pimdecfgtioc.c
    vx
    cY
    cxr
    clt
    vx
    cY
    @4
    pimdecfgtioc.y
    @3
    vx
    cA
    nfrab1
    nfcxfr
    #
    vx
    cxr
    nfcv
    vx
    clt
    nfcv
    #
    nfsup
    nfcxfr
    #
    vx
    cA
    nfcv
    vx
    cR
    @13
    clt
    vx
    cR
    nfcv
    @18
    vx
    cS
    cF
    vx
    cF
    nfcv
    @19
    nffv
    nfbr
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
    breq2d
    elrabf
    sylib
    simprd
    adantr
    @10
    @16
    @1
    vy
    cv
    #
    cle
    wbr
    #
    @20
    cF
    cfv
    #
    @2
    cle
    wbr
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    @1
    cS
    cle
    wbr
    #
    @13
    @2
    cle
    wbr
    #
    @10
    @16
    @25
    wph
    @16
    @9
    @14
    adantr
    wph
    @9
    @11
    @25
    @12
    wph
    @25
    vx
    cA
    pimdecfgtioc.i
    r19.21bi
    syldan
    jca
    @10
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
    cioc
    co
    #
    wcel
    #
    @26
    @28
    @10
    mnfxr
    a1i
    wph
    @29
    @9
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
    pimdecfgtioc.e
    sseldd
    sseldi
    adantr
    @9
    @31
    wph
    @9
    @1
    cI
    @30
    @1
    cI
    cA
    elinel1
    pimdecfgtioc.d
    syl6eleq
    adantl
    cmnf
    cS
    @1
    iocleub
    syl3anc
    @24
    @26
    @27
    wi
    vy
    cS
    cA
    @20
    cS
    wceq
    #
    @21
    @26
    @23
    @27
    @20
    cS
    @1
    cle
    breq2
    @32
    @22
    @13
    @2
    cle
    @20
    cS
    cF
    fveq2
    breq1d
    imbi12d
    rspcva
    sylc
    xrltletrd
    jca
    @3
    vx
    cY
    cA
    pimdecfgtioc.y
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
    vz
    cv
    @0
    wcel
    vx
    nfv
    nfci
    @17
    dfss3f
    sylibr
    eqssd
end
