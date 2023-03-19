include "cv.mm"
include "csb.mm"
include "cmpt.mm"
include "cfv.mm"
include "ccur.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "csbcom.mm"
include "csbco.mm"
include "csbeq2i.mm"
include "eqtri.mm"
include "3eqtri.mm"
include "wral.mm"
include "wa.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc2.mm"
include "imp.mm"
include "syl21anc.mm"
include "syl5eqel.mm"
include "eqid.mm"
include "fvmpts.mm"
include "syl2anc.mm"
include "cmpt2.mm"
include "nfcv.mm"
include "nfcsb.mm"
include "weq.mm"
include "sylan9eq.mm"
include "cbvmpt2.mm"
include "mpan9.mm"
include "ralrimivva.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "syl.mm"
include "mpt2curryvald.mm"
include "fveq1d.mm"
include "a1i.mm"
include "csbid.mm"
include "eqtr2i.mm"
include "csbeq2dv.mm"
include "3eqtr3g.mm"
include "csbeq1.mm"
include "adantr.mm"
include "adantl.mm"
include "eqtrd.mm"
include "eqidd.mm"
include "nfv.mm"
include "nfcxfr.mm"
include "ovmpt2dxf.mm"
include "3eqtr4d.mm"

theorem fvmpt2curryd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume fvmpt2curryd.f: |- F = ( x e. X , y e. Y |-> C )
  assume fvmpt2curryd.c: |- ( ph -> A. x e. X A. y e. Y C e. V )
  assume fvmpt2curryd.y: |- ( ph -> Y e. W )
  assume fvmpt2curryd.a: |- ( ph -> A e. X )
  assume fvmpt2curryd.b: |- ( ph -> B e. Y )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint V x
  disjoint V y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ph x
  disjoint ph y
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
  disjoint F a
  disjoint F b
  disjoint V a
  disjoint V b
  disjoint X a
  disjoint X b
  disjoint Y a
  disjoint Y b
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> ( ( curry F ` A ) ` B ) = ( A F B ) )

  proof
    wph
    cB
    vb
    cY
    va
    cA
    vy
    vb
    cv
    #
    vx
    va
    cv
    #
    cC
    csb
    #
    csb
    #
    csb
    #
    cmpt
    #
    cfv
    #
    vb
    cB
    @4
    csb
    #
    cB
    cA
    cF
    ccur
    cfv
    #
    cfv
    cA
    cB
    cF
    co
    wph
    cB
    cY
    wcel
    #
    @7
    cV
    wcel
    @6
    @7
    wceq
    fvmpt2curryd.b
    wph
    @7
    vy
    cB
    vx
    cA
    cC
    csb
    #
    csb
    #
    cV
    @7
    va
    cA
    vb
    cB
    @3
    csb
    #
    csb
    va
    cA
    vy
    cB
    @2
    csb
    #
    csb
    #
    @11
    vb
    va
    cB
    cA
    @3
    csbcom
    va
    cA
    @12
    @13
    vy
    vb
    cB
    @2
    csbco
    csbeq2i
    @14
    vy
    cB
    va
    cA
    @2
    csb
    #
    csb
    @11
    va
    vy
    cA
    cB
    @2
    csbcom
    vy
    cB
    @15
    @10
    vx
    va
    cA
    cC
    csbco
    csbeq2i
    eqtri
    3eqtri
    #
    wph
    cA
    cX
    wcel
    #
    @9
    cC
    cV
    wcel
    #
    vy
    cY
    wral
    vx
    cX
    wral
    #
    @11
    cV
    wcel
    #
    fvmpt2curryd.a
    fvmpt2curryd.b
    fvmpt2curryd.c
    @17
    @9
    wa
    @19
    @20
    @18
    @20
    @10
    cV
    wcel
    vx
    vy
    cA
    cB
    cX
    cY
    vx
    @10
    cV
    vx
    cA
    cC
    nfcsb1v
    nfel1
    vy
    @11
    cV
    vy
    cB
    @10
    nfcsb1v
    #
    nfel1
    vx
    cv
    #
    cA
    wceq
    #
    cC
    @10
    cV
    vx
    cA
    cC
    csbeq1a
    eleq1d
    vy
    cv
    #
    cB
    wceq
    #
    @10
    @11
    cV
    vy
    cB
    @10
    csbeq1a
    eleq1d
    rspc2
    imp
    syl21anc
    syl5eqel
    #
    vb
    cB
    @4
    cY
    @5
    cV
    @5
    eqid
    fvmpts
    syl2anc
    wph
    cB
    @8
    @5
    wph
    va
    vb
    cA
    @3
    cF
    cV
    cW
    cX
    cY
    cF
    vx
    vy
    cX
    cY
    cC
    cmpt2
    #
    va
    vb
    cX
    cY
    @3
    cmpt2
    fvmpt2curryd.f
    vx
    vy
    va
    vb
    cX
    cY
    cC
    @3
    va
    cC
    nfcv
    vb
    cC
    nfcv
    vx
    vy
    @0
    @2
    vx
    @0
    nfcv
    vx
    @1
    cC
    nfcsb1v
    #
    nfcsb
    #
    vy
    @0
    @2
    nfcsb1v
    #
    vx
    va
    weq
    #
    vy
    vb
    weq
    #
    cC
    @2
    @3
    vx
    @1
    cC
    csbeq1a
    #
    vy
    @0
    @2
    csbeq1a
    #
    sylan9eq
    cbvmpt2
    eqtri
    wph
    @3
    cV
    wcel
    #
    va
    vb
    cX
    cY
    wph
    @19
    @1
    cX
    wcel
    @0
    cY
    wcel
    wa
    @35
    fvmpt2curryd.c
    @18
    @35
    @2
    cV
    wcel
    vx
    vy
    @1
    @0
    cX
    cY
    vx
    @2
    cV
    @28
    nfel1
    vy
    @3
    cV
    @30
    nfel1
    @31
    cC
    @2
    cV
    @33
    eleq1d
    @32
    @2
    @3
    cV
    @34
    eleq1d
    rspc2
    mpan9
    ralrimivva
    wph
    @9
    cY
    c0
    wne
    fvmpt2curryd.b
    cY
    cB
    ne0i
    syl
    fvmpt2curryd.y
    fvmpt2curryd.a
    mpt2curryvald
    fveq1d
    wph
    vx
    vy
    cA
    cB
    cX
    cY
    cC
    @7
    cF
    cY
    cV
    cF
    @27
    wceq
    wph
    fvmpt2curryd.f
    a1i
    wph
    @23
    @25
    wa
    #
    cC
    vb
    @24
    va
    @22
    @3
    csb
    #
    csb
    #
    @7
    wph
    va
    @22
    @2
    csb
    #
    va
    @22
    vb
    @24
    @3
    csb
    #
    csb
    cC
    @38
    wph
    va
    @22
    @2
    @40
    @2
    @40
    wceq
    wph
    @40
    vy
    @24
    @2
    csb
    @2
    vy
    vb
    @24
    @2
    csbco
    vy
    @2
    csbid
    eqtr2i
    a1i
    csbeq2dv
    @39
    vx
    @22
    cC
    csb
    cC
    vx
    va
    @22
    cC
    csbco
    vx
    cC
    csbid
    eqtri
    va
    vb
    @22
    @24
    @3
    csbcom
    3eqtr3g
    @36
    @38
    vb
    @24
    @4
    csb
    #
    @7
    @36
    vb
    @24
    @37
    @4
    @23
    @37
    @4
    wceq
    @25
    va
    @22
    cA
    @3
    csbeq1
    adantr
    csbeq2dv
    @25
    @41
    @7
    wceq
    @23
    vb
    @24
    cB
    @4
    csbeq1
    adantl
    eqtrd
    sylan9eq
    wph
    @23
    wa
    cY
    eqidd
    fvmpt2curryd.a
    fvmpt2curryd.b
    @26
    wph
    vx
    nfv
    wph
    vy
    nfv
    vy
    cA
    nfcv
    vx
    cB
    nfcv
    #
    vx
    vb
    cB
    @4
    @42
    vx
    va
    cA
    @3
    vx
    cA
    nfcv
    @29
    nfcsb
    nfcsb
    vy
    @7
    @11
    @16
    @21
    nfcxfr
    ovmpt2dxf
    3eqtr4d
end
