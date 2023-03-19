include "cfn.mm"
include "wcel.mm"
include "cn.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wn.mm"
include "crab.mm"
include "simpll.mm"
include "simplr.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "cbvralv.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "oveq2.mm"
include "cbvrex2v.mm"
include "raleqdv.mm"
include "2rexbidv.mm"
include "notbid.mm"
include "cbvrabv.mm"
include "c0.mm"
include "wne.mm"
include "simpr.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "eleq2d.mm"
include "cbvrexv.mm"
include "sylnib.mm"
include "rabn0.mm"
include "rexnal.mm"
include "bitri.mm"
include "ralbii.mm"
include "ralnex.mm"
include "sylibr.mm"
include "vdwnnlem3.mm"
include "iman.mm"
include "mpbir.mm"

theorem vdwnn
  let cR: class R
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint a c
  disjoint a d
  disjoint a k
  disjoint a m
  disjoint F a
  disjoint c d
  disjoint c k
  disjoint c m
  disjoint F c
  disjoint d k
  disjoint d m
  disjoint F d
  disjoint k m
  disjoint F k
  disjoint F m
  disjoint R c
  disjoint a u
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint c u
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint d u
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint R u
  disjoint R y
  disjoint R z
  assert |- ( ( R e. Fin /\ F : NN --> R ) -> E. c e. R A. k e. NN E. a e. NN E. d e. NN A. m e. ( 0 ... ( k - 1 ) ) ( a + ( m x. d ) ) e. ( `' F " { c } ) )

  proof
    cR
    cfn
    wcel
    #
    cn
    cR
    cF
    wf
    #
    wa
    #
    va
    cv
    #
    vm
    cv
    #
    vd
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    cF
    ccnv
    #
    vc
    cv
    #
    csn
    #
    cima
    #
    wcel
    #
    vm
    cc0
    vk
    cv
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    vd
    cn
    wrex
    va
    cn
    wrex
    #
    vk
    cn
    wral
    #
    vc
    cR
    wrex
    #
    wi
    @2
    @19
    wn
    #
    wa
    #
    wn
    @21
    cR
    @7
    @8
    vu
    cv
    #
    csn
    #
    cima
    #
    wcel
    #
    vm
    @15
    wral
    #
    vd
    cn
    wrex
    va
    cn
    wrex
    #
    wn
    #
    vk
    cn
    crab
    #
    vx
    vw
    cF
    vy
    vu
    vz
    @0
    @1
    @20
    simpll
    @0
    @1
    @20
    simplr
    @28
    vy
    cv
    #
    vw
    cv
    #
    vz
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    @24
    wcel
    #
    vw
    cc0
    vx
    cv
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    vz
    cn
    wrex
    vy
    cn
    wrex
    #
    wn
    vk
    vx
    cn
    vk
    vx
    weq
    #
    @27
    @40
    @27
    @35
    vw
    @15
    wral
    #
    vz
    cn
    wrex
    vy
    cn
    wrex
    @41
    @40
    @26
    @42
    @30
    @31
    @5
    cmul
    co
    #
    caddc
    co
    #
    @24
    wcel
    #
    vw
    @15
    wral
    #
    va
    vd
    vy
    vz
    cn
    cn
    @26
    @3
    @43
    caddc
    co
    #
    @24
    wcel
    #
    vw
    @15
    wral
    va
    vy
    weq
    #
    @46
    @25
    @48
    vm
    vw
    @15
    vm
    vw
    weq
    #
    @7
    @47
    @24
    @50
    @6
    @43
    @3
    caddc
    @4
    @31
    @5
    cmul
    oveq1
    oveq2d
    eleq1d
    cbvralv
    @49
    @48
    @45
    vw
    @15
    @49
    @47
    @44
    @24
    @3
    @30
    @43
    caddc
    oveq1
    eleq1d
    ralbidv
    syl5bb
    vd
    vz
    weq
    #
    @45
    @35
    vw
    @15
    @51
    @44
    @34
    @24
    @51
    @43
    @33
    @30
    caddc
    @5
    @32
    @31
    cmul
    oveq2
    oveq2d
    eleq1d
    ralbidv
    cbvrex2v
    @41
    @42
    @39
    vy
    vz
    cn
    cn
    @41
    @35
    vw
    @15
    @38
    @41
    @14
    @37
    cc0
    cfz
    @13
    @36
    c1
    cmin
    oveq1
    oveq2d
    raleqdv
    2rexbidv
    syl5bb
    notbid
    cbvrabv
    @21
    @27
    vk
    cn
    wral
    #
    vu
    cR
    wrex
    #
    wn
    #
    @29
    c0
    wne
    #
    vu
    cR
    wral
    #
    @21
    @19
    @53
    @2
    @20
    simpr
    @18
    @52
    vc
    vu
    cR
    vc
    vu
    weq
    #
    @17
    @27
    vk
    cn
    @57
    @16
    @26
    va
    vd
    cn
    cn
    @57
    @12
    @25
    vm
    @15
    @57
    @11
    @24
    @7
    @57
    @10
    @23
    @8
    @9
    @22
    sneq
    imaeq2d
    eleq2d
    ralbidv
    2rexbidv
    ralbidv
    cbvrexv
    sylnib
    @56
    @52
    wn
    #
    vu
    cR
    wral
    @54
    @55
    @58
    vu
    cR
    @55
    @28
    vk
    cn
    wrex
    @58
    @28
    vk
    cn
    rabn0
    @27
    vk
    cn
    rexnal
    bitri
    ralbii
    @52
    vu
    cR
    ralnex
    bitri
    sylibr
    vdwnnlem3
    @2
    @19
    iman
    mpbir
end
