include "wcel.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cpw.mm"
include "wral.mm"
include "w3a.mm"
include "wceq.mm"
include "crab.mm"
include "cint.mm"
include "pwidg.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "fveq2.mm"
include "id.mm"
include "sseq12d.mm"
include "intminss.mm"
include "syl2anc.mm"
include "syl5eqss.mm"
include "wi.mm"
include "wa.mm"
include "adantl.mm"
include "vex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "simprl.mm"
include "simpl3.mm"
include "pweq.mm"
include "sseq2d.mm"
include "raleqbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "sseq1d.mm"
include "simprr.mm"
include "sstrd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ssintrab.mm"
include "cbvrabv.mm"
include "inteqi.mm"
include "eqtri.mm"
include "syl6sseqr.mm"
include "sselpwd.mm"
include "simp3.mm"
include "fvex.mm"
include "elpw.mm"
include "eqssd.mm"
include "jca.mm"

theorem knatar
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let cV: class V
  let cX: class X
  let vw: setvar w
  assume knatar.1: |- X = |^| { z e. ~P A | ( F ` z ) C_ z }

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint X x
  disjoint X y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint F w
  disjoint V w
  disjoint X w
  assert |- ( ( A e. V /\ ( F ` A ) C_ A /\ A. x e. ~P A A. y e. ~P x ( F ` y ) C_ ( F ` x ) ) -> ( X C_ A /\ ( F ` X ) = X ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cF
    cfv
    #
    cA
    wss
    #
    vy
    cv
    #
    cF
    cfv
    #
    vx
    cv
    #
    cF
    cfv
    #
    wss
    #
    vy
    @5
    cpw
    #
    wral
    #
    vx
    cA
    cpw
    #
    wral
    #
    w3a
    #
    cX
    cA
    wss
    cX
    cF
    cfv
    #
    cX
    wceq
    @12
    cX
    vz
    cv
    #
    cF
    cfv
    #
    @14
    wss
    #
    vz
    @10
    crab
    #
    cint
    #
    cA
    knatar.1
    @12
    cA
    @10
    wcel
    #
    @2
    @18
    cA
    wss
    @0
    @2
    @19
    @11
    cA
    cV
    pwidg
    3ad2ant1
    #
    @0
    @2
    @11
    simp2
    #
    @16
    @2
    vz
    cA
    @10
    @14
    cA
    wceq
    #
    @15
    @1
    @14
    cA
    @14
    cA
    cF
    fveq2
    @22
    id
    sseq12d
    intminss
    syl2anc
    syl5eqss
    #
    @12
    @13
    cX
    @12
    @13
    vw
    cv
    #
    cF
    cfv
    #
    @24
    wss
    #
    vw
    @10
    crab
    #
    cint
    #
    cX
    @12
    @26
    @13
    @24
    wss
    #
    wi
    #
    vw
    @10
    wral
    @13
    @28
    wss
    @12
    @30
    vw
    @10
    @12
    @24
    @10
    wcel
    #
    @26
    @29
    @12
    @31
    @26
    wa
    #
    wa
    #
    @13
    @25
    @24
    @33
    cX
    @24
    cpw
    #
    wcel
    #
    @4
    @25
    wss
    #
    vy
    @34
    wral
    #
    @13
    @25
    wss
    #
    @33
    cX
    @24
    wss
    @35
    @33
    cX
    @18
    @24
    knatar.1
    @32
    @18
    @24
    wss
    @12
    @16
    @26
    vz
    @24
    @10
    @14
    @24
    wceq
    #
    @15
    @25
    @14
    @24
    @14
    @24
    cF
    fveq2
    @39
    id
    sseq12d
    #
    intminss
    adantl
    syl5eqss
    cX
    @24
    vw
    vex
    elpw2
    sylibr
    @33
    @31
    @11
    @37
    @12
    @31
    @26
    simprl
    @0
    @2
    @11
    @32
    simpl3
    @9
    @37
    vx
    @24
    @10
    @5
    @24
    wceq
    #
    @7
    @36
    vy
    @8
    @34
    @5
    @24
    pweq
    @41
    @6
    @25
    @4
    @5
    @24
    cF
    fveq2
    sseq2d
    raleqbidv
    rspcv
    sylc
    @36
    @38
    vy
    cX
    @34
    @3
    cX
    wceq
    #
    @4
    @13
    @25
    @3
    cX
    cF
    fveq2
    #
    sseq1d
    rspcv
    sylc
    @12
    @31
    @26
    simprr
    sstrd
    expr
    ralrimiva
    @26
    vw
    @13
    @10
    ssintrab
    sylibr
    cX
    @18
    @28
    knatar.1
    @17
    @27
    @16
    @26
    vz
    vw
    @10
    @40
    cbvrabv
    inteqi
    eqtri
    #
    syl6sseqr
    #
    @12
    cX
    @28
    @13
    @44
    @12
    @13
    @10
    wcel
    #
    @13
    cF
    cfv
    #
    @13
    wss
    #
    @28
    @13
    wss
    @12
    @13
    cA
    wss
    @46
    @12
    @13
    @1
    cA
    @12
    cX
    @10
    wcel
    #
    @4
    @1
    wss
    #
    vy
    @10
    wral
    #
    @13
    @1
    wss
    #
    @12
    cX
    cA
    @10
    @20
    @23
    sselpwd
    #
    @12
    @19
    @11
    @51
    @20
    @0
    @2
    @11
    simp3
    #
    @9
    @51
    vx
    cA
    @10
    @5
    cA
    wceq
    #
    @7
    @50
    vy
    @8
    @10
    @5
    cA
    pweq
    @55
    @6
    @1
    @4
    @5
    cA
    cF
    fveq2
    sseq2d
    raleqbidv
    rspcv
    sylc
    @50
    @52
    vy
    cX
    @10
    @42
    @4
    @13
    @1
    @43
    sseq1d
    rspcv
    sylc
    @21
    sstrd
    @13
    cA
    cX
    cF
    fvex
    #
    elpw
    sylibr
    @12
    @13
    cX
    cpw
    #
    wcel
    #
    @4
    @13
    wss
    #
    vy
    @57
    wral
    #
    @48
    @12
    @13
    cX
    wss
    @58
    @45
    @13
    cX
    @56
    elpw
    sylibr
    @12
    @49
    @11
    @60
    @53
    @54
    @9
    @60
    vx
    cX
    @10
    @5
    cX
    wceq
    #
    @7
    @59
    vy
    @8
    @57
    @5
    cX
    pweq
    @61
    @6
    @13
    @4
    @5
    cX
    cF
    fveq2
    sseq2d
    raleqbidv
    rspcv
    sylc
    @59
    @48
    vy
    @13
    @57
    @3
    @13
    wceq
    @4
    @47
    @13
    @3
    @13
    cF
    fveq2
    sseq1d
    rspcv
    sylc
    @26
    @48
    vw
    @13
    @10
    @24
    @13
    wceq
    #
    @25
    @47
    @24
    @13
    @24
    @13
    cF
    fveq2
    @62
    id
    sseq12d
    intminss
    syl2anc
    syl5eqss
    eqssd
    jca
end
