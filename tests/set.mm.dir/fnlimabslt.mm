include "cv.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cdm.mm"
include "ciin.mm"
include "ciun.mm"
include "eqid.mm"
include "cmpt.mm"
include "cli.mm"
include "crab.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfdm.mm"
include "nfiin.mm"
include "nfiun.mm"
include "nfv.mm"
include "nfmpt.mm"
include "nfel.mm"
include "wceq.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "cbvrab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "allbutfifvre.mm"
include "cc.mm"
include "fnlimcnv.mm"
include "cvv.mm"
include "fveq1d.mm"
include "cbvmpt.mm"
include "a1i.mm"
include "adantl.mm"
include "simpr.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "climd.mm"
include "nfmpt1.mm"
include "nfii1.mm"
include "nfrab.mm"
include "nfcxfr.mm"
include "nfov.mm"
include "nfbr.mm"
include "nfan.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "cbvral.mm"
include "rexbii.mm"
include "sylibr.mm"
include "wi.mm"
include "ralimdaa.mm"
include "reximdva.mm"
include "mpd.mm"
include "jca.mm"
include "rexanuz2.mm"

theorem fnlimabslt
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vj: setvar j
  let vl: setvar l
  let vy: setvar y
  assume fnlimabslt.p: |- F/ m ph
  assume fnlimabslt.f: |- F/_ m F
  assume fnlimabslt.n: |- F/_ x F
  assume fnlimabslt.m: |- ( ph -> M e. ZZ )
  assume fnlimabslt.z: |- Z = ( ZZ>= ` M )
  assume fnlimabslt.b: |- ( ( ph /\ m e. Z ) -> ( F ` m ) : dom ( F ` m ) --> RR )
  assume fnlimabslt.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( m e. Z |-> ( ( F ` m ) ` x ) ) e. dom ~~> }
  assume fnlimabslt.g: |- G = ( x e. D |-> ( ~~> ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )
  assume fnlimabslt.x: |- ( ph -> X e. D )
  assume fnlimabslt.y: |- ( ph -> Y e. RR+ )

  disjoint F n
  disjoint G n
  disjoint M n
  disjoint X m
  disjoint X n
  disjoint m n
  disjoint Y m
  disjoint Y n
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint m x
  disjoint n x
  disjoint n ph
  disjoint F j
  disjoint F l
  disjoint j l
  disjoint j n
  disjoint F y
  disjoint n y
  disjoint G j
  disjoint X j
  disjoint X l
  disjoint j m
  disjoint l m
  disjoint Y j
  disjoint Z j
  disjoint Z l
  disjoint Z y
  disjoint m y
  disjoint x y
  disjoint j ph
  disjoint l ph
  assert |- ( ph -> E. n e. Z A. m e. ( ZZ>= ` n ) ( ( ( F ` m ) ` X ) e. RR /\ ( abs ` ( ( ( F ` m ) ` X ) - ( G ` X ) ) ) < Y ) )

  proof
    wph
    cX
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cr
    wcel
    #
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    wral
    vn
    cZ
    wrex
    #
    @2
    cX
    cG
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cY
    clt
    wbr
    #
    vm
    @5
    wral
    #
    vn
    cZ
    wrex
    #
    wa
    @3
    @10
    wa
    vm
    @5
    wral
    vn
    cZ
    wrex
    wph
    @6
    @12
    wph
    vn
    cZ
    vm
    @5
    @1
    cdm
    #
    ciin
    #
    ciun
    #
    vm
    vn
    cF
    cM
    cX
    cZ
    fnlimabslt.p
    fnlimabslt.z
    fnlimabslt.b
    @15
    eqid
    wph
    cD
    @15
    cX
    cD
    vm
    cZ
    vx
    cv
    #
    @1
    cfv
    #
    cmpt
    #
    cli
    cdm
    #
    wcel
    #
    vx
    @15
    crab
    #
    @15
    fnlimabslt.d
    @21
    vm
    cZ
    vy
    cv
    #
    @1
    cfv
    #
    cmpt
    #
    @19
    wcel
    #
    vy
    @15
    crab
    @15
    @20
    @25
    vx
    vy
    @15
    vn
    vx
    cZ
    @14
    vx
    cZ
    nfcv
    #
    vm
    vx
    @5
    @13
    vx
    @5
    nfcv
    vx
    @1
    vx
    @0
    cF
    fnlimabslt.n
    vx
    @0
    nfcv
    nffv
    #
    nfdm
    nfiin
    nfiun
    vy
    @15
    nfcv
    @20
    vy
    nfv
    vx
    @24
    @19
    vx
    vm
    cZ
    @23
    @26
    vx
    @22
    @1
    @27
    vx
    @22
    nfcv
    nffv
    nfmpt
    vx
    @19
    nfcv
    nfel
    @16
    @22
    wceq
    #
    @18
    @24
    @19
    @28
    vm
    cZ
    @17
    @23
    @16
    @22
    @1
    fveq2
    mpteq2dv
    eleq1d
    cbvrab
    @25
    vy
    @15
    ssrab2
    eqsstri
    eqsstri
    fnlimabslt.x
    sseldi
    allbutfifvre
    wph
    @2
    cc
    wcel
    #
    @10
    wa
    #
    vm
    @5
    wral
    #
    vn
    cZ
    wrex
    #
    @12
    wph
    cX
    vj
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cc
    wcel
    #
    @35
    @7
    cmin
    co
    #
    cabs
    cfv
    #
    cY
    clt
    wbr
    #
    wa
    #
    vj
    @5
    wral
    #
    vn
    cZ
    wrex
    @32
    wph
    @7
    @35
    vn
    vj
    vm
    cZ
    @2
    cmpt
    #
    cM
    cY
    cZ
    wph
    vj
    nfv
    vj
    @42
    nfcv
    fnlimabslt.z
    fnlimabslt.m
    wph
    vx
    cD
    vm
    vn
    cF
    cG
    cX
    cZ
    fnlimabslt.n
    fnlimabslt.d
    fnlimabslt.g
    fnlimabslt.x
    fnlimcnv
    wph
    @33
    cZ
    wcel
    #
    wa
    #
    vl
    @33
    cX
    vl
    cv
    #
    cF
    cfv
    #
    cfv
    #
    @35
    cZ
    @42
    cvv
    @42
    vl
    cZ
    @47
    cmpt
    wceq
    @44
    vm
    vl
    cZ
    @2
    @47
    vl
    @2
    nfcv
    vm
    cX
    @46
    vm
    @45
    cF
    fnlimabslt.f
    vm
    @45
    nfcv
    nffv
    vm
    cX
    nfcv
    #
    nffv
    @0
    @45
    wceq
    cX
    @1
    @46
    @0
    @45
    cF
    fveq2
    fveq1d
    cbvmpt
    a1i
    @45
    @33
    wceq
    #
    @47
    @35
    wceq
    @44
    @49
    cX
    @46
    @34
    @45
    @33
    cF
    fveq2
    fveq1d
    adantl
    wph
    @43
    simpr
    @44
    cX
    @34
    fvexd
    fvmptd
    fnlimabslt.y
    climd
    @31
    @41
    vn
    cZ
    @30
    @40
    vm
    vj
    @5
    @30
    vj
    nfv
    @36
    @39
    vm
    vm
    @35
    cc
    vm
    cX
    @34
    vm
    @33
    cF
    fnlimabslt.f
    vm
    @33
    nfcv
    nffv
    @48
    nffv
    #
    vm
    cc
    nfcv
    nfel
    vm
    @38
    cY
    clt
    vm
    @37
    cabs
    vm
    cabs
    nfcv
    vm
    @35
    @7
    cmin
    @50
    vm
    cmin
    nfcv
    vm
    cX
    cG
    vm
    cG
    vx
    cD
    @18
    cli
    cfv
    #
    cmpt
    fnlimabslt.g
    vm
    vx
    cD
    @51
    vm
    cD
    @21
    fnlimabslt.d
    @20
    vm
    vx
    @15
    vm
    @18
    @19
    vm
    cZ
    @17
    nfmpt1
    #
    vm
    @19
    nfcv
    nfel
    vn
    vm
    cZ
    @14
    vm
    cZ
    nfcv
    vm
    @5
    @13
    nfii1
    nfiun
    nfrab
    nfcxfr
    vm
    @18
    cli
    vm
    cli
    nfcv
    @52
    nffv
    nfmpt
    nfcxfr
    @48
    nffv
    nfov
    nffv
    vm
    clt
    nfcv
    vm
    cY
    nfcv
    nfbr
    nfan
    @0
    @33
    wceq
    #
    @29
    @36
    @10
    @39
    @53
    @2
    @35
    cc
    @53
    cX
    @1
    @34
    @0
    @33
    cF
    fveq2
    fveq1d
    #
    eleq1d
    @53
    @9
    @38
    cY
    clt
    @53
    @8
    @37
    cabs
    @53
    @2
    @35
    @7
    cmin
    @54
    oveq1d
    fveq2d
    breq1d
    anbi12d
    cbvral
    rexbii
    sylibr
    wph
    @31
    @11
    vn
    cZ
    wph
    @4
    cZ
    wcel
    #
    wa
    #
    @30
    @10
    vm
    @5
    wph
    @55
    vm
    fnlimabslt.p
    @55
    vm
    nfv
    nfan
    @30
    @10
    wi
    @56
    @0
    @5
    wcel
    wa
    @29
    @10
    simpr
    a1i
    ralimdaa
    reximdva
    mpd
    jca
    @3
    @10
    vn
    vm
    cM
    cZ
    fnlimabslt.z
    rexanuz2
    sylibr
end
