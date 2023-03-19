include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "cdv.mm"
include "cv.mm"
include "csb.mm"
include "caddc.mm"
include "wceq.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfov.mm"
include "csbeq1a.mm"
include "oveq12d.mm"
include "cbvmpt.mm"
include "oveq2i.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "nfcsb1.mm"
include "nfel.mm"
include "csbco.mm"
include "csbid.mm"
include "eqtri.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "eqcom.mm"
include "imbi1i.mm"
include "imbi2i.mm"
include "bitri.mm"
include "mpbi.mm"
include "dvmptmul.mm"

theorem dvmptmulf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cV: class V
  let cW: class W
  let cX: class X
  let vy: setvar y
  let vk: setvar k
  assume dvmptmulf.ph: |- F/ x ph
  assume dvmptmulf.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptmulf.a: |- ( ( ph /\ x e. X ) -> A e. CC )
  assume dvmptmulf.b: |- ( ( ph /\ x e. X ) -> B e. V )
  assume dvmptmulf.ab: |- ( ph -> ( S _D ( x e. X |-> A ) ) = ( x e. X |-> B ) )
  assume dvmptmulf.c: |- ( ( ph /\ x e. X ) -> C e. CC )
  assume dvmptmulf.d: |- ( ( ph /\ x e. X ) -> D e. W )
  assume dvmptmulf.cd: |- ( ph -> ( S _D ( x e. X |-> C ) ) = ( x e. X |-> D ) )

  disjoint V x
  disjoint W x
  disjoint X x
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint D y
  disjoint S y
  disjoint V y
  disjoint x y
  disjoint W y
  disjoint X y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( S _D ( x e. X |-> ( A x. C ) ) ) = ( x e. X |-> ( ( B x. C ) + ( D x. A ) ) ) )

  proof
    wph
    cS
    vx
    cX
    cA
    cC
    cmul
    co
    #
    cmpt
    #
    cdv
    co
    #
    cS
    vy
    cX
    vx
    vy
    cv
    #
    cA
    csb
    #
    vx
    @3
    cC
    csb
    #
    cmul
    co
    #
    cmpt
    #
    cdv
    co
    #
    vy
    cX
    vx
    @3
    cB
    csb
    #
    @5
    cmul
    co
    #
    vx
    @3
    cD
    csb
    #
    @4
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    vx
    cX
    cB
    cC
    cmul
    co
    #
    cD
    cA
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    @2
    @8
    wceq
    wph
    @1
    @7
    cS
    cdv
    vx
    vy
    cX
    @0
    @6
    vy
    @0
    nfcv
    vx
    @4
    @5
    cmul
    vx
    @3
    cA
    nfcsb1v
    #
    vx
    cmul
    nfcv
    #
    vx
    @3
    cC
    nfcsb1v
    #
    nfov
    vx
    cv
    #
    @3
    wceq
    #
    cA
    @4
    cC
    @5
    cmul
    vx
    @3
    cA
    csbeq1a
    #
    vx
    @3
    cC
    csbeq1a
    #
    oveq12d
    cbvmpt
    oveq2i
    a1i
    wph
    vy
    @4
    @9
    @5
    @11
    cS
    cV
    cW
    cX
    dvmptmulf.s
    wph
    @22
    cX
    wcel
    #
    wa
    #
    cA
    cc
    wcel
    #
    wi
    wph
    @3
    cX
    wcel
    #
    wa
    #
    @4
    cc
    wcel
    #
    wi
    vx
    vy
    @30
    @31
    vx
    wph
    @29
    vx
    dvmptmulf.ph
    @29
    vx
    nfv
    nfan
    #
    vx
    @4
    cc
    @19
    nfel1
    nfim
    @23
    @27
    @30
    @28
    @31
    @23
    @26
    @29
    wph
    @22
    @3
    cX
    eleq1
    anbi2d
    #
    @23
    cA
    @4
    cc
    @24
    eleq1d
    imbi12d
    dvmptmulf.a
    chvar
    @27
    cB
    cV
    wcel
    #
    wi
    @30
    @9
    cV
    wcel
    #
    wi
    vx
    vy
    @30
    @35
    vx
    @32
    vx
    @9
    cV
    vx
    @3
    cB
    vx
    @3
    nfcv
    #
    nfcsb1
    #
    vx
    cV
    nfcv
    nfel
    nfim
    @23
    @27
    @30
    @34
    @35
    @33
    @23
    cB
    @9
    cV
    vx
    @3
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    dvmptmulf.b
    chvar
    wph
    cS
    vy
    cX
    @4
    cmpt
    #
    cdv
    co
    #
    cS
    vx
    cX
    cA
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    cB
    cmpt
    #
    vy
    cX
    @9
    cmpt
    #
    @40
    @42
    wceq
    wph
    @39
    @41
    cS
    cdv
    vy
    vx
    cX
    @4
    cA
    @19
    vy
    cA
    nfcv
    @3
    @22
    wceq
    #
    @4
    vy
    @22
    @4
    csb
    #
    cA
    vy
    @22
    @4
    csbeq1a
    @46
    cA
    wceq
    @45
    @46
    vx
    @22
    cA
    csb
    cA
    vx
    vy
    @22
    cA
    csbco
    vx
    cA
    csbid
    eqtri
    a1i
    eqtrd
    #
    cbvmpt
    oveq2i
    a1i
    dvmptmulf.ab
    @43
    @44
    wceq
    wph
    vx
    vy
    cX
    cB
    @9
    vy
    cB
    nfcv
    @37
    @38
    cbvmpt
    a1i
    3eqtrd
    @27
    cC
    cc
    wcel
    #
    wi
    @30
    @5
    cc
    wcel
    #
    wi
    vx
    vy
    @30
    @49
    vx
    @32
    vx
    @5
    cc
    @21
    nfel1
    nfim
    @23
    @27
    @30
    @48
    @49
    @33
    @23
    cC
    @5
    cc
    @25
    eleq1d
    imbi12d
    dvmptmulf.c
    chvar
    @27
    cD
    cW
    wcel
    #
    wi
    @30
    @11
    cW
    wcel
    #
    wi
    vx
    vy
    @30
    @51
    vx
    @32
    vx
    @11
    cW
    vx
    @3
    cD
    @36
    nfcsb1
    #
    vx
    cW
    nfcv
    nfel
    nfim
    @23
    @27
    @30
    @50
    @51
    @33
    @23
    cD
    @11
    cW
    vx
    @3
    cD
    csbeq1a
    #
    eleq1d
    imbi12d
    dvmptmulf.d
    chvar
    wph
    cS
    vy
    cX
    @5
    cmpt
    #
    cdv
    co
    #
    cS
    vx
    cX
    cC
    cmpt
    #
    cdv
    co
    #
    vx
    cX
    cD
    cmpt
    #
    vy
    cX
    @11
    cmpt
    #
    @55
    @57
    wceq
    wph
    @54
    @56
    cS
    cdv
    vy
    vx
    cX
    @5
    cC
    @21
    vy
    cC
    nfcv
    @23
    cC
    @5
    wceq
    #
    wi
    #
    @45
    @5
    cC
    wceq
    #
    wi
    #
    @25
    @61
    @45
    @60
    wi
    @63
    @23
    @45
    @60
    @22
    @3
    eqcom
    #
    imbi1i
    @60
    @62
    @45
    cC
    @5
    eqcom
    imbi2i
    bitri
    mpbi
    #
    cbvmpt
    oveq2i
    a1i
    dvmptmulf.cd
    @58
    @59
    wceq
    wph
    vx
    vy
    cX
    cD
    @11
    vy
    cD
    nfcv
    @52
    @53
    cbvmpt
    a1i
    3eqtrd
    dvmptmul
    @14
    @18
    wceq
    wph
    vy
    vx
    cX
    @13
    @17
    vx
    @10
    @12
    caddc
    vx
    @9
    @5
    cmul
    @37
    @20
    @21
    nfov
    vx
    caddc
    nfcv
    vx
    @11
    @4
    cmul
    @52
    @20
    @19
    nfov
    nfov
    vy
    @17
    nfcv
    @45
    @10
    @15
    @12
    @16
    caddc
    @45
    @9
    cB
    @5
    cC
    cmul
    @23
    cB
    @9
    wceq
    #
    wi
    #
    @45
    @9
    cB
    wceq
    #
    wi
    #
    @38
    @67
    @45
    @66
    wi
    @69
    @23
    @45
    @66
    @64
    imbi1i
    @66
    @68
    @45
    cB
    @9
    eqcom
    imbi2i
    bitri
    mpbi
    @65
    oveq12d
    @45
    @11
    cD
    @4
    cA
    cmul
    @23
    cD
    @11
    wceq
    #
    wi
    #
    @45
    @11
    cD
    wceq
    #
    wi
    #
    @53
    @71
    @45
    @70
    wi
    @73
    @23
    @45
    @70
    @64
    imbi1i
    @70
    @72
    @45
    cD
    @11
    eqcom
    imbi2i
    bitri
    mpbi
    @47
    oveq12d
    oveq12d
    cbvmpt
    a1i
    3eqtrd
end
