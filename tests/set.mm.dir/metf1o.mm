include "wcel.mm"
include "cme.mm"
include "cfv.mm"
include "wf1o.mm"
include "w3a.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "f1of.mm"
include "ffvelrn.mm"
include "ex.mm"
include "anim12d.mm"
include "syl.mm"
include "metcl.mm"
include "3expib.mm"
include "sylan9r.mm"
include "3adant1.mm"
include "ralrimivv.mm"
include "fmpt2.mm"
include "sylib.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "imp.mm"
include "adantll.mm"
include "meteq0.mm"
include "3expb.mm"
include "adantlr.mm"
include "syldan.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1fveq.mm"
include "sylan.mm"
include "3bitrd.mm"
include "mettri2.mm"
include "expcom.mm"
include "ancoms.mm"
include "impcom.mm"
include "anassrs.mm"
include "adantr.mm"
include "oveq12d.mm"
include "breq12d.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "jca.mm"
include "3adantl1.mm"
include "ismet.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"

theorem metf1o
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume metf1o.2: |- N = ( x e. Y , y e. Y |-> ( ( F ` x ) M ( F ` y ) ) )

  disjoint M x
  disjoint M y
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint F x
  disjoint F y
  disjoint A x
  disjoint A y
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint w x
  disjoint w y
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint N u
  disjoint N v
  disjoint N w
  assert |- ( ( Y e. A /\ M e. ( Met ` X ) /\ F : Y -1-1-onto-> X ) -> N e. ( Met ` Y ) )

  proof
    cY
    cA
    wcel
    #
    cM
    cX
    cme
    cfv
    wcel
    #
    cY
    cX
    cF
    wf1o
    #
    w3a
    #
    cN
    cY
    cme
    cfv
    wcel
    #
    cY
    cY
    cxp
    cr
    cN
    wf
    #
    vu
    cv
    #
    vv
    cv
    #
    cN
    co
    #
    cc0
    wceq
    #
    @6
    @7
    wceq
    #
    wb
    #
    @8
    vw
    cv
    #
    @6
    cN
    co
    #
    @12
    @7
    cN
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    vw
    cY
    wral
    #
    wa
    #
    vv
    cY
    wral
    vu
    cY
    wral
    #
    @3
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    cM
    co
    #
    cr
    wcel
    #
    vy
    cY
    wral
    vx
    cY
    wral
    @5
    @3
    @25
    vx
    vy
    cY
    cY
    @1
    @2
    @20
    cY
    wcel
    #
    @22
    cY
    wcel
    #
    wa
    #
    @25
    wi
    @0
    @2
    @28
    @21
    cX
    wcel
    #
    @23
    cX
    wcel
    #
    wa
    #
    @1
    @25
    @2
    cY
    cX
    cF
    wf
    #
    @28
    @31
    wi
    cY
    cX
    cF
    f1of
    #
    @32
    @26
    @29
    @27
    @30
    @32
    @26
    @29
    cY
    cX
    @20
    cF
    ffvelrn
    ex
    @32
    @27
    @30
    cY
    cX
    @22
    cF
    ffvelrn
    ex
    anim12d
    syl
    @1
    @29
    @30
    @25
    @21
    @23
    cM
    cX
    metcl
    3expib
    sylan9r
    3adant1
    ralrimivv
    vx
    vy
    cY
    cY
    @24
    cr
    cN
    metf1o.2
    fmpt2
    sylib
    @3
    @18
    vu
    vv
    cY
    cY
    @3
    @6
    cY
    wcel
    #
    @7
    cY
    wcel
    #
    wa
    #
    @18
    @1
    @2
    @36
    @18
    @0
    @1
    @2
    wa
    #
    @36
    wa
    #
    @11
    @17
    @38
    @9
    @6
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    cM
    co
    #
    cc0
    wceq
    #
    @39
    @40
    wceq
    #
    @10
    @36
    @9
    @42
    wb
    @37
    @36
    @8
    @41
    cc0
    vx
    vy
    @6
    @7
    cY
    cY
    @24
    @41
    cN
    @39
    @23
    cM
    co
    @20
    @6
    wceq
    @21
    @39
    @23
    cM
    @20
    @6
    cF
    fveq2
    oveq1d
    @22
    @7
    wceq
    #
    @23
    @40
    @39
    cM
    @22
    @7
    cF
    fveq2
    #
    oveq2d
    metf1o.2
    @39
    @40
    cM
    ovex
    ovmpt2
    #
    eqeq1d
    adantl
    @37
    @36
    @39
    cX
    wcel
    #
    @40
    cX
    wcel
    #
    wa
    #
    @42
    @43
    wb
    #
    @2
    @36
    @49
    @1
    @2
    @36
    @49
    @2
    @32
    @36
    @49
    wi
    @33
    @32
    @34
    @47
    @35
    @48
    @32
    @34
    @47
    cY
    cX
    @6
    cF
    ffvelrn
    ex
    @32
    @35
    @48
    cY
    cX
    @7
    cF
    ffvelrn
    ex
    anim12d
    #
    syl
    imp
    adantll
    @1
    @49
    @50
    @2
    @1
    @47
    @48
    @50
    @39
    @40
    cM
    cX
    meteq0
    3expb
    adantlr
    syldan
    @2
    @36
    @43
    @10
    wb
    #
    @1
    @2
    cY
    cX
    cF
    wf1
    @36
    @52
    cY
    cX
    cF
    f1of1
    cY
    cX
    @6
    @7
    cF
    f1fveq
    sylan
    adantll
    3bitrd
    @38
    @16
    vw
    cY
    @38
    @12
    cY
    wcel
    #
    wa
    @16
    @41
    @12
    cF
    cfv
    #
    @39
    cM
    co
    #
    @54
    @40
    cM
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    @37
    @36
    @53
    @58
    @37
    @36
    @53
    wa
    #
    @49
    @54
    cX
    wcel
    #
    wa
    #
    @58
    @2
    @59
    @61
    @1
    @2
    @59
    @61
    @2
    @32
    @59
    @61
    wi
    @33
    @32
    @36
    @49
    @53
    @60
    @51
    @32
    @53
    @60
    cY
    cX
    @12
    cF
    ffvelrn
    ex
    anim12d
    syl
    imp
    adantll
    @1
    @61
    @58
    @2
    @61
    @1
    @58
    @60
    @49
    @1
    @58
    wi
    #
    @60
    @47
    @48
    @62
    @1
    @60
    @47
    @48
    w3a
    @58
    @39
    @40
    @54
    cM
    cX
    mettri2
    expcom
    3expb
    ancoms
    impcom
    adantlr
    syldan
    anassrs
    @36
    @53
    @16
    @58
    wb
    @37
    @59
    @8
    @41
    @15
    @57
    cle
    @36
    @8
    @41
    wceq
    @53
    @46
    adantr
    @59
    @13
    @55
    @14
    @56
    caddc
    @34
    @53
    @13
    @55
    wceq
    #
    @35
    @53
    @34
    @63
    vx
    vy
    @12
    @6
    cY
    cY
    @24
    @55
    cN
    @54
    @23
    cM
    co
    #
    @20
    @12
    wceq
    @21
    @54
    @23
    cM
    @20
    @12
    cF
    fveq2
    oveq1d
    #
    @22
    @6
    wceq
    @23
    @39
    @54
    cM
    @22
    @6
    cF
    fveq2
    oveq2d
    metf1o.2
    @54
    @39
    cM
    ovex
    ovmpt2
    ancoms
    adantlr
    @35
    @53
    @14
    @56
    wceq
    #
    @34
    @53
    @35
    @66
    vx
    vy
    @12
    @7
    cY
    cY
    @24
    @56
    cN
    @64
    @65
    @44
    @23
    @40
    @54
    cM
    @45
    oveq2d
    metf1o.2
    @54
    @40
    cM
    ovex
    ovmpt2
    ancoms
    adantll
    oveq12d
    breq12d
    adantll
    mpbird
    ralrimiva
    jca
    3adantl1
    ex
    ralrimivv
    @0
    @1
    @4
    @5
    @19
    wa
    wb
    @2
    vu
    vv
    vw
    cA
    cN
    cY
    ismet
    3ad2ant1
    mpbir2and
end
