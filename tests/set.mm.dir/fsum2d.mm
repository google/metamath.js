include "wss.mm"
include "csu.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wceq.mm"
include "ssid.mm"
include "cfn.mm"
include "wcel.mm"
include "wi.mm"
include "c0.mm"
include "cun.mm"
include "sseq1.mm"
include "sumeq1.mm"
include "iuneq1.mm"
include "sumeq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "cc0.mm"
include "sum0.mm"
include "0iun.mm"
include "sumeq1i.mm"
include "3eqtr4ri.mm"
include "2a1i.mm"
include "wn.mm"
include "wa.mm"
include "ssun1.mm"
include "sstr.mm"
include "mpan.mm"
include "imim1i.mm"
include "simpll.mm"
include "syl.mm"
include "sylan.mm"
include "cc.mm"
include "simplr.mm"
include "simpr.mm"
include "biid.mm"
include "fsum2dlem.mm"
include "exp31.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "adantl.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpi.mm"

theorem fsum2d
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume fsum2d.1: |- ( z = <. j , k >. -> D = C )
  assume fsum2d.2: |- ( ph -> A e. Fin )
  assume fsum2d.3: |- ( ( ph /\ j e. A ) -> B e. Fin )
  assume fsum2d.4: |- ( ( ph /\ ( j e. A /\ k e. B ) ) -> C e. CC )

  disjoint j k
  disjoint j z
  disjoint A j
  disjoint k z
  disjoint A k
  disjoint A z
  disjoint B k
  disjoint B z
  disjoint D j
  disjoint D k
  disjoint C z
  disjoint j ph
  disjoint k ph
  disjoint ph z
  disjoint j m
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint k m
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint B m
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint D m
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint C m
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint m ph
  disjoint ph w
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> sum_ j e. A sum_ k e. B C = sum_ z e. U_ j e. A ( { j } X. B ) D )

  proof
    wph
    cA
    cA
    wss
    #
    cA
    cB
    cC
    vk
    csu
    #
    vj
    csu
    #
    vj
    cA
    vj
    cv
    #
    csn
    cB
    cxp
    #
    ciun
    #
    cD
    vz
    csu
    #
    wceq
    #
    cA
    ssid
    cA
    cfn
    wcel
    #
    wph
    @0
    @7
    wi
    #
    fsum2d.2
    wph
    vw
    cv
    #
    cA
    wss
    #
    @10
    @1
    vj
    csu
    #
    vj
    @10
    @4
    ciun
    #
    cD
    vz
    csu
    #
    wceq
    #
    wi
    #
    wi
    wph
    c0
    cA
    wss
    #
    c0
    @1
    vj
    csu
    #
    vj
    c0
    @4
    ciun
    #
    cD
    vz
    csu
    #
    wceq
    #
    wi
    #
    wi
    wph
    vx
    cv
    #
    cA
    wss
    #
    @23
    @1
    vj
    csu
    #
    vj
    @23
    @4
    ciun
    #
    cD
    vz
    csu
    #
    wceq
    #
    wi
    #
    wi
    #
    wph
    @23
    vy
    cv
    #
    csn
    #
    cun
    #
    cA
    wss
    #
    @33
    @1
    vj
    csu
    #
    vj
    @33
    @4
    ciun
    #
    cD
    vz
    csu
    #
    wceq
    #
    wi
    #
    wi
    #
    wph
    @9
    wi
    vw
    vx
    vy
    cA
    @10
    c0
    wceq
    #
    @16
    @22
    wph
    @41
    @11
    @17
    @15
    @21
    @10
    c0
    cA
    sseq1
    @41
    @12
    @18
    @14
    @20
    @10
    c0
    @1
    vj
    sumeq1
    @41
    @13
    @19
    cD
    vz
    vj
    @10
    c0
    @4
    iuneq1
    sumeq1d
    eqeq12d
    imbi12d
    imbi2d
    @10
    @23
    wceq
    #
    @16
    @29
    wph
    @42
    @11
    @24
    @15
    @28
    @10
    @23
    cA
    sseq1
    @42
    @12
    @25
    @14
    @27
    @10
    @23
    @1
    vj
    sumeq1
    @42
    @13
    @26
    cD
    vz
    vj
    @10
    @23
    @4
    iuneq1
    sumeq1d
    eqeq12d
    imbi12d
    imbi2d
    @10
    @33
    wceq
    #
    @16
    @39
    wph
    @43
    @11
    @34
    @15
    @38
    @10
    @33
    cA
    sseq1
    @43
    @12
    @35
    @14
    @37
    @10
    @33
    @1
    vj
    sumeq1
    @43
    @13
    @36
    cD
    vz
    vj
    @10
    @33
    @4
    iuneq1
    sumeq1d
    eqeq12d
    imbi12d
    imbi2d
    @10
    cA
    wceq
    #
    @16
    @9
    wph
    @44
    @11
    @0
    @15
    @7
    @10
    cA
    cA
    sseq1
    @44
    @12
    @2
    @14
    @6
    @10
    cA
    @1
    vj
    sumeq1
    @44
    @13
    @5
    cD
    vz
    vj
    @10
    cA
    @4
    iuneq1
    sumeq1d
    eqeq12d
    imbi12d
    imbi2d
    @21
    wph
    @17
    c0
    cD
    vz
    csu
    cc0
    @20
    @18
    cD
    vz
    sum0
    @19
    c0
    cD
    vz
    vj
    @4
    0iun
    sumeq1i
    @1
    vj
    sum0
    3eqtr4ri
    2a1i
    @31
    @23
    wcel
    wn
    #
    @30
    @40
    wi
    @23
    cfn
    wcel
    @45
    wph
    @29
    @39
    wph
    @45
    @29
    @39
    wi
    @29
    @34
    @28
    wi
    wph
    @45
    wa
    #
    @39
    @34
    @24
    @28
    @23
    @33
    wss
    @34
    @24
    @23
    @32
    ssun1
    @23
    @33
    cA
    sstr
    mpan
    imim1i
    @46
    @34
    @28
    @38
    @46
    @34
    @28
    @38
    @46
    @34
    wa
    #
    @28
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    vj
    vk
    fsum2d.1
    @47
    wph
    @8
    wph
    @45
    @34
    simpll
    #
    fsum2d.2
    syl
    @47
    wph
    @3
    cA
    wcel
    #
    cB
    cfn
    wcel
    @48
    fsum2d.3
    sylan
    @47
    wph
    @49
    vk
    cv
    cB
    wcel
    wa
    cC
    cc
    wcel
    @48
    fsum2d.4
    sylan
    wph
    @45
    @34
    simplr
    @46
    @34
    simpr
    @28
    biid
    fsum2dlem
    exp31
    a2d
    syl5
    expcom
    a2d
    adantl
    findcard2s
    mpcom
    mpi
end
