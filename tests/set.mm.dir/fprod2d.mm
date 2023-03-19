include "wss.mm"
include "cprod.mm"
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
include "prodeq1.mm"
include "iuneq1.mm"
include "0iun.mm"
include "syl6eq.mm"
include "prodeq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "c1.mm"
include "prod0.mm"
include "eqtr4i.mm"
include "2a1i.mm"
include "wel.mm"
include "wn.mm"
include "wa.mm"
include "ssun1.mm"
include "sstr.mm"
include "mpan.mm"
include "imim1i.mm"
include "ad2antrr.mm"
include "adantlr.mm"
include "cc.mm"
include "simplr.mm"
include "simpr.mm"
include "biid.mm"
include "fprod2dlem.mm"
include "exp31.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "adantl.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpi.mm"

theorem fprod2d
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume fprod2d.1: |- ( z = <. j , k >. -> D = C )
  assume fprod2d.2: |- ( ph -> A e. Fin )
  assume fprod2d.3: |- ( ( ph /\ j e. A ) -> B e. Fin )
  assume fprod2d.4: |- ( ( ph /\ ( j e. A /\ k e. B ) ) -> C e. CC )

  disjoint A j
  disjoint A k
  disjoint A z
  disjoint B k
  disjoint B z
  disjoint C z
  disjoint D j
  disjoint D k
  disjoint j k
  disjoint j ph
  disjoint j z
  disjoint k ph
  disjoint k z
  disjoint ph z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( ph -> prod_ j e. A prod_ k e. B C = prod_ z e. U_ j e. A ( { j } X. B ) D )

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
    cprod
    #
    vj
    cprod
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
    cprod
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
    fprod2d.2
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
    cprod
    #
    vj
    @10
    @4
    ciun
    #
    cD
    vz
    cprod
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
    cprod
    #
    c0
    cD
    vz
    cprod
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
    @22
    @1
    vj
    cprod
    #
    vj
    @22
    @4
    ciun
    #
    cD
    vz
    cprod
    #
    wceq
    #
    wi
    #
    wi
    #
    wph
    @22
    vy
    cv
    csn
    #
    cun
    #
    cA
    wss
    #
    @31
    @1
    vj
    cprod
    #
    vj
    @31
    @4
    ciun
    #
    cD
    vz
    cprod
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
    @21
    wph
    @39
    @11
    @17
    @15
    @20
    @10
    c0
    cA
    sseq1
    @39
    @12
    @18
    @14
    @19
    @10
    c0
    @1
    vj
    prodeq1
    @39
    @13
    c0
    cD
    vz
    @39
    @13
    vj
    c0
    @4
    ciun
    c0
    vj
    @10
    c0
    @4
    iuneq1
    vj
    @4
    0iun
    syl6eq
    prodeq1d
    eqeq12d
    imbi12d
    imbi2d
    vw
    vx
    weq
    #
    @16
    @28
    wph
    @40
    @11
    @23
    @15
    @27
    @10
    @22
    cA
    sseq1
    @40
    @12
    @24
    @14
    @26
    @10
    @22
    @1
    vj
    prodeq1
    @40
    @13
    @25
    cD
    vz
    vj
    @10
    @22
    @4
    iuneq1
    prodeq1d
    eqeq12d
    imbi12d
    imbi2d
    @10
    @31
    wceq
    #
    @16
    @37
    wph
    @41
    @11
    @32
    @15
    @36
    @10
    @31
    cA
    sseq1
    @41
    @12
    @33
    @14
    @35
    @10
    @31
    @1
    vj
    prodeq1
    @41
    @13
    @34
    cD
    vz
    vj
    @10
    @31
    @4
    iuneq1
    prodeq1d
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
    @42
    @11
    @0
    @15
    @7
    @10
    cA
    cA
    sseq1
    @42
    @12
    @2
    @14
    @6
    @10
    cA
    @1
    vj
    prodeq1
    @42
    @13
    @5
    cD
    vz
    vj
    @10
    cA
    @4
    iuneq1
    prodeq1d
    eqeq12d
    imbi12d
    imbi2d
    @20
    wph
    @17
    @18
    c1
    @19
    @1
    vj
    prod0
    cD
    vz
    prod0
    eqtr4i
    2a1i
    vy
    vx
    wel
    wn
    #
    @29
    @38
    wi
    @22
    cfn
    wcel
    @43
    wph
    @28
    @37
    wph
    @43
    @28
    @37
    wi
    @28
    @32
    @27
    wi
    wph
    @43
    wa
    #
    @37
    @32
    @23
    @27
    @22
    @31
    wss
    @32
    @23
    @22
    @30
    ssun1
    @22
    @31
    cA
    sstr
    mpan
    imim1i
    @44
    @32
    @27
    @36
    @44
    @32
    @27
    @36
    @44
    @32
    wa
    @27
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    vj
    vk
    fprod2d.1
    wph
    @8
    @43
    @32
    fprod2d.2
    ad2antrr
    @44
    @3
    cA
    wcel
    #
    cB
    cfn
    wcel
    #
    @32
    wph
    @45
    @46
    @43
    fprod2d.3
    adantlr
    adantlr
    @44
    @45
    vk
    cv
    cB
    wcel
    wa
    #
    cC
    cc
    wcel
    #
    @32
    wph
    @47
    @48
    @43
    fprod2d.4
    adantlr
    adantlr
    wph
    @43
    @32
    simplr
    @44
    @32
    simpr
    @27
    biid
    fprod2dlem
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
