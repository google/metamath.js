include "cr.mm"
include "cn0.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cabs.mm"
include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "cvv.mm"
include "nn0uz.mm"
include "0zd.mm"
include "wcel.mm"
include "reex.mm"
include "a1i.mm"
include "knoppcnlem5.mm"
include "nn0ex.mm"
include "mptex.mm"
include "wa.mm"
include "wceq.mm"
include "eqid.mm"
include "simpr.mm"
include "oveq2d.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "recnd.mm"
include "abscld.mm"
include "adantr.mm"
include "reexpcld.mm"
include "eqeltrd.mm"
include "cle.mm"
include "fveq2d.mm"
include "mpteq2dv.mm"
include "adantrr.mm"
include "fveq1d.mm"
include "simprr.mm"
include "fvexd.mm"
include "cn.mm"
include "knoppcnlem4.mm"
include "eqbrtrd.mm"
include "caddc.mm"
include "cseq.mm"
include "c1.mm"
include "cmin.mm"
include "cdiv.mm"
include "cli.mm"
include "wbr.mm"
include "cdm.mm"
include "clt.mm"
include "cc.mm"
include "absidm.mm"
include "syl.mm"
include "geolim.mm"
include "seqex.mm"
include "ovex.mm"
include "breldm.mm"
include "mtest.mm"

theorem knoppcnlem6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cT: class T
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vk: setvar k
  let vw: setvar w
  assume knoppcnlem6.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppcnlem6.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppcnlem6.n: |- ( ph -> N e. NN )
  assume knoppcnlem6.1: |- ( ph -> C e. RR )
  assume knoppcnlem6.2: |- ( ph -> ( abs ` C ) < 1 )

  disjoint C m
  disjoint C n
  disjoint C y
  disjoint m n
  disjoint m y
  disjoint n y
  disjoint F m
  disjoint F z
  disjoint m z
  disjoint N n
  disjoint N y
  disjoint N x
  disjoint T n
  disjoint T y
  disjoint m ph
  disjoint n ph
  disjoint ph y
  disjoint ph z
  disjoint n z
  disjoint y z
  disjoint m x
  disjoint x z
  disjoint C k
  disjoint C w
  disjoint k m
  disjoint k n
  disjoint k w
  disjoint k y
  disjoint m w
  disjoint n w
  disjoint w y
  disjoint F k
  disjoint F w
  disjoint k z
  disjoint w z
  disjoint k ph
  disjoint ph w
  disjoint k x
  disjoint w x
  assert |- ( ph -> seq 0 ( oF + , ( m e. NN0 |-> ( z e. RR |-> ( ( F ` z ) ` m ) ) ) ) e. dom ( ~~>u ` RR ) )

  proof
    wph
    vw
    cr
    vk
    vm
    cn0
    vz
    cr
    vm
    cv
    #
    vz
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    cmpt
    #
    vm
    cn0
    cC
    cabs
    cfv
    #
    @0
    cexp
    co
    #
    cmpt
    #
    cc0
    cvv
    cvv
    cn0
    nn0uz
    wph
    0zd
    cr
    cvv
    wcel
    wph
    reex
    a1i
    wph
    vx
    vy
    vz
    cC
    cT
    vm
    vn
    cF
    cN
    knoppcnlem6.t
    knoppcnlem6.f
    knoppcnlem6.n
    knoppcnlem6.1
    knoppcnlem5
    @8
    cvv
    wcel
    wph
    vm
    cn0
    @7
    nn0ex
    mptex
    a1i
    wph
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @9
    @8
    cfv
    #
    @6
    @9
    cexp
    co
    #
    cr
    @11
    vm
    @9
    @7
    @13
    cn0
    @8
    cvv
    @8
    @8
    wceq
    @11
    @8
    eqid
    a1i
    @11
    @0
    @9
    wceq
    #
    wa
    @0
    @9
    @6
    cexp
    @11
    @14
    simpr
    oveq2d
    wph
    @10
    simpr
    #
    @11
    @6
    @9
    cexp
    ovexd
    fvmptd
    #
    @11
    @6
    @9
    wph
    @6
    cr
    wcel
    @10
    wph
    cC
    wph
    cC
    knoppcnlem6.1
    recnd
    #
    abscld
    #
    adantr
    @15
    reexpcld
    eqeltrd
    wph
    @10
    vw
    cv
    #
    cr
    wcel
    #
    wa
    #
    wa
    #
    @19
    @9
    @5
    cfv
    #
    cfv
    #
    cabs
    cfv
    @9
    @19
    cF
    cfv
    #
    cfv
    #
    cabs
    cfv
    @12
    cle
    @22
    @24
    @26
    cabs
    @22
    vz
    @19
    @9
    @2
    cfv
    #
    @26
    cr
    @23
    cvv
    @22
    vm
    @9
    @4
    vz
    cr
    @27
    cmpt
    #
    cn0
    @5
    cvv
    @5
    @5
    wceq
    @22
    @5
    eqid
    a1i
    @22
    @14
    wa
    #
    vz
    cr
    @3
    @27
    @29
    @0
    @9
    @2
    @22
    @14
    simpr
    fveq2d
    mpteq2dv
    wph
    @10
    @10
    @20
    @15
    adantrr
    #
    @28
    cvv
    wcel
    @22
    vz
    cr
    @27
    reex
    mptex
    a1i
    fvmptd
    @22
    @1
    @19
    wceq
    #
    wa
    #
    @9
    @2
    @25
    @32
    @1
    @19
    cF
    @22
    @31
    simpr
    fveq2d
    fveq1d
    wph
    @10
    @20
    simprr
    #
    @22
    @9
    @25
    fvexd
    fvmptd
    fveq2d
    @22
    vx
    vy
    @19
    cC
    cT
    vm
    vn
    cF
    @9
    cN
    knoppcnlem6.t
    knoppcnlem6.f
    wph
    cN
    cn
    wcel
    @21
    knoppcnlem6.n
    adantr
    wph
    cC
    cr
    wcel
    @21
    knoppcnlem6.1
    adantr
    @33
    @30
    knoppcnlem4
    eqbrtrd
    wph
    caddc
    @8
    cc0
    cseq
    #
    c1
    c1
    @6
    cmin
    co
    #
    cdiv
    co
    #
    cli
    wbr
    @34
    cli
    cdm
    wcel
    wph
    @6
    vk
    @8
    wph
    @6
    @18
    recnd
    wph
    @6
    cabs
    cfv
    #
    @6
    c1
    clt
    wph
    cC
    cc
    wcel
    @37
    @6
    wceq
    @17
    cC
    absidm
    syl
    knoppcnlem6.2
    eqbrtrd
    @16
    geolim
    @34
    @36
    cli
    caddc
    @8
    cc0
    seqex
    c1
    @35
    cdiv
    ovex
    breldm
    syl
    mtest
end
