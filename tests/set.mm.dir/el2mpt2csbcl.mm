include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "co.mm"
include "csb.mm"
include "wi.mm"
include "simpl.mm"
include "cmpt2.mm"
include "cv.mm"
include "cvv.mm"
include "wceq.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfmpt2.mm"
include "nfcsb.mm"
include "csbeq1a.mm"
include "csbeq2dv.mm"
include "sylan9eq.mm"
include "mpt2eq123dv.mm"
include "cbvmpt2.mm"
include "eqtri.mm"
include "a1i.mm"
include "csbeq1.mm"
include "adantr.mm"
include "adantl.mm"
include "eqtrd.mm"
include "simpr.mm"
include "ralimi.mm"
include "rspcsbela.mm"
include "syl2an.mm"
include "ex.mm"
include "ralimdv.mm"
include "impcom.mm"
include "syl2anc.mm"
include "mpt2exga.mm"
include "ovmpt2d.mm"
include "oveqd.mm"
include "eleq2d.mm"
include "eqid.mm"
include "elmpt2cl.mm"
include "syl6bi.mm"
include "impancom.mm"
include "jca.mm"
include "wn.mm"
include "c0.mm"
include "mpt2ndm0.mm"
include "noel.mm"
include "pm2.21i.mm"
include "0ov.mm"
include "eleq2s.mm"
include "adantld.mm"
include "pm2.61i.mm"

theorem el2mpt2csbcl
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  assume el2mpt2csbcl.o: |- O = ( x e. A , y e. B |-> ( s e. C , t e. D |-> E ) )

  disjoint A s
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint B s
  disjoint B t
  disjoint B x
  disjoint B y
  disjoint C s
  disjoint C t
  disjoint D s
  disjoint D t
  disjoint U x
  disjoint U y
  disjoint V x
  disjoint V y
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint Y s
  disjoint Y t
  disjoint Y x
  disjoint Y y
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a s
  disjoint a t
  disjoint a x
  disjoint a y
  disjoint b s
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
  disjoint D a
  disjoint D b
  disjoint E a
  disjoint E b
  disjoint U a
  disjoint U b
  disjoint V a
  disjoint V b
  disjoint X a
  disjoint X b
  disjoint Y a
  disjoint Y b
  assert |- ( A. x e. A A. y e. B ( C e. U /\ D e. V ) -> ( W e. ( S ( X O Y ) T ) -> ( ( X e. A /\ Y e. B ) /\ ( S e. [_ X / x ]_ [_ Y / y ]_ C /\ T e. [_ X / x ]_ [_ Y / y ]_ D ) ) ) )

  proof
    cC
    cU
    wcel
    #
    cD
    cV
    wcel
    #
    wa
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    cW
    cS
    cT
    cX
    cY
    cO
    co
    #
    co
    #
    wcel
    #
    cX
    cA
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cS
    vx
    cX
    vy
    cY
    cC
    csb
    #
    csb
    #
    wcel
    cT
    vx
    cX
    vy
    cY
    cD
    csb
    #
    csb
    #
    wcel
    wa
    #
    wa
    #
    @10
    @4
    @7
    wa
    #
    @16
    wi
    @10
    @17
    @16
    @10
    @17
    wa
    @10
    @15
    @10
    @17
    simpl
    @17
    @10
    @15
    @4
    @10
    @7
    @15
    @4
    @10
    wa
    #
    @7
    cW
    cS
    cT
    vs
    vt
    @12
    @14
    vx
    cX
    vy
    cY
    cE
    csb
    #
    csb
    #
    cmpt2
    #
    co
    #
    wcel
    @15
    @18
    @6
    @22
    cW
    @18
    @5
    @21
    cS
    cT
    @18
    va
    vb
    cX
    cY
    cA
    cB
    vs
    vt
    vx
    va
    cv
    #
    vy
    vb
    cv
    #
    cC
    csb
    #
    csb
    #
    vx
    @23
    vy
    @24
    cD
    csb
    #
    csb
    #
    vx
    @23
    vy
    @24
    cE
    csb
    #
    csb
    #
    cmpt2
    #
    @21
    cO
    cvv
    cO
    va
    vb
    cA
    cB
    @31
    cmpt2
    #
    wceq
    @18
    cO
    vx
    vy
    cA
    cB
    vs
    vt
    cC
    cD
    cE
    cmpt2
    #
    cmpt2
    @32
    el2mpt2csbcl.o
    vx
    vy
    va
    vb
    cA
    cB
    @33
    @31
    va
    @33
    nfcv
    vb
    @33
    nfcv
    vs
    vt
    vx
    @26
    @28
    @30
    vx
    @23
    @25
    nfcsb1v
    vx
    @23
    @27
    nfcsb1v
    vx
    @23
    @29
    nfcsb1v
    nfmpt2
    vs
    vt
    vy
    @26
    @28
    @30
    vy
    vx
    @23
    @25
    vy
    @23
    nfcv
    #
    vy
    @24
    cC
    nfcsb1v
    nfcsb
    vy
    vx
    @23
    @27
    @34
    vy
    @24
    cD
    nfcsb1v
    nfcsb
    vy
    vx
    @23
    @29
    @34
    vy
    @24
    cE
    nfcsb1v
    nfcsb
    nfmpt2
    vx
    cv
    @23
    wceq
    #
    vy
    cv
    @24
    wceq
    #
    wa
    vs
    vt
    cC
    cD
    cE
    @26
    @28
    @30
    @35
    @36
    cC
    vx
    @23
    cC
    csb
    @26
    vx
    @23
    cC
    csbeq1a
    @36
    vx
    @23
    cC
    @25
    vy
    @24
    cC
    csbeq1a
    csbeq2dv
    sylan9eq
    @35
    @36
    cD
    vx
    @23
    cD
    csb
    @28
    vx
    @23
    cD
    csbeq1a
    @36
    vx
    @23
    cD
    @27
    vy
    @24
    cD
    csbeq1a
    csbeq2dv
    sylan9eq
    @35
    @36
    cE
    vx
    @23
    cE
    csb
    @30
    vx
    @23
    cE
    csbeq1a
    @36
    vx
    @23
    cE
    @29
    vy
    @24
    cE
    csbeq1a
    csbeq2dv
    sylan9eq
    mpt2eq123dv
    cbvmpt2
    eqtri
    a1i
    @23
    cX
    wceq
    #
    @24
    cY
    wceq
    #
    wa
    #
    @31
    @21
    wceq
    @18
    @39
    vs
    vt
    @26
    @28
    @30
    @12
    @14
    @20
    @39
    @26
    vx
    cX
    @25
    csb
    #
    @12
    @37
    @26
    @40
    wceq
    @38
    vx
    @23
    cX
    @25
    csbeq1
    adantr
    @39
    vx
    cX
    @25
    @11
    @38
    @25
    @11
    wceq
    @37
    vy
    @24
    cY
    cC
    csbeq1
    adantl
    csbeq2dv
    eqtrd
    @39
    @28
    vx
    cX
    @27
    csb
    #
    @14
    @37
    @28
    @41
    wceq
    @38
    vx
    @23
    cX
    @27
    csbeq1
    adantr
    @39
    vx
    cX
    @27
    @13
    @38
    @27
    @13
    wceq
    @37
    vy
    @24
    cY
    cD
    csbeq1
    adantl
    csbeq2dv
    eqtrd
    @39
    @30
    vx
    cX
    @29
    csb
    #
    @20
    @37
    @30
    @42
    wceq
    @38
    vx
    @23
    cX
    @29
    csbeq1
    adantr
    @39
    vx
    cX
    @29
    @19
    @38
    @29
    @19
    wceq
    @37
    vy
    @24
    cY
    cE
    csbeq1
    adantl
    csbeq2dv
    eqtrd
    mpt2eq123dv
    adantl
    @10
    @8
    @4
    @8
    @9
    simpl
    adantl
    #
    @10
    @9
    @4
    @8
    @9
    simpr
    #
    adantl
    @18
    @12
    cU
    wcel
    #
    @14
    cV
    wcel
    #
    @21
    cvv
    wcel
    @18
    @8
    @11
    cU
    wcel
    #
    vx
    cA
    wral
    #
    @45
    @43
    @10
    @4
    @48
    @10
    @3
    @47
    vx
    cA
    @10
    @3
    @47
    @10
    @9
    @0
    vy
    cB
    wral
    @47
    @3
    @44
    @2
    @0
    vy
    cB
    @0
    @1
    simpl
    ralimi
    vy
    cY
    cB
    cC
    cU
    rspcsbela
    syl2an
    ex
    ralimdv
    impcom
    vx
    cX
    cA
    @11
    cU
    rspcsbela
    syl2anc
    @18
    @8
    @13
    cV
    wcel
    #
    vx
    cA
    wral
    #
    @46
    @43
    @10
    @4
    @50
    @10
    @3
    @49
    vx
    cA
    @10
    @3
    @49
    @10
    @9
    @1
    vy
    cB
    wral
    @49
    @3
    @44
    @2
    @1
    vy
    cB
    @0
    @1
    simpr
    ralimi
    vy
    cY
    cB
    cD
    cV
    rspcsbela
    syl2an
    ex
    ralimdv
    impcom
    vx
    cX
    cA
    @13
    cV
    rspcsbela
    syl2anc
    vs
    vt
    @12
    @14
    @20
    cU
    cV
    mpt2exga
    syl2anc
    ovmpt2d
    oveqd
    eleq2d
    vs
    vt
    @12
    @14
    @20
    cS
    cT
    @21
    cW
    @21
    eqid
    elmpt2cl
    syl6bi
    impancom
    impcom
    jca
    ex
    @10
    wn
    #
    @7
    @16
    @4
    @51
    @7
    cW
    cS
    cT
    c0
    co
    #
    wcel
    @16
    @51
    @6
    @52
    cW
    @51
    @5
    c0
    cS
    cT
    vx
    vy
    @33
    cO
    cX
    cY
    cA
    cB
    el2mpt2csbcl.o
    mpt2ndm0
    oveqd
    eleq2d
    @16
    cW
    c0
    @52
    cW
    c0
    wcel
    @16
    cW
    noel
    pm2.21i
    cS
    cT
    0ov
    eleq2s
    syl6bi
    adantld
    pm2.61i
    ex
end
