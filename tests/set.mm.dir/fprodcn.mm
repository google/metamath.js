include "cv.mm"
include "cprod.mm"
include "cmpt.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "prodeq1.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "c1.mm"
include "prod0.mm"
include "mpteq2i.mm"
include "eqidd.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "a1i.mm"
include "cc.mm"
include "ctopon.mm"
include "cfv.mm"
include "cnfldtopon.mm"
include "1cnd.mm"
include "cnmptc.mm"
include "eqeltrd.mm"
include "wss.mm"
include "cdif.mm"
include "wa.mm"
include "csb.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfcprod.mm"
include "csbeq1a.mm"
include "prodeq2ad.mm"
include "cbvmpt.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcprod1.mm"
include "nfmpt.mm"
include "nfel.mm"
include "ad2antrr.mm"
include "cfn.mm"
include "eqcomi.mm"
include "ad4ant14.mm"
include "simplrl.mm"
include "simplrr.mm"
include "prodeq2sdv.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "adantl.mm"
include "fprodcnlem.mm"
include "ex.mm"
include "findcard2d.mm"

theorem fprodcn
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cJ: class J
  let cK: class K
  let cX: class X
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume fprodcn.d: |- F/ k ph
  assume fprodcn.k: |- K = ( TopOpen ` CCfld )
  assume fprodcn.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume fprodcn.a: |- ( ph -> A e. Fin )
  assume fprodcn.b: |- ( ( ph /\ k e. A ) -> ( x e. X |-> B ) e. ( J Cn K ) )

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint J k
  disjoint K k
  disjoint X k
  disjoint X x
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( x e. X |-> prod_ k e. A B ) e. ( J Cn K ) )

  proof
    wph
    vx
    cX
    vy
    cv
    #
    cB
    vk
    cprod
    #
    cmpt
    #
    cJ
    cK
    ccn
    co
    #
    wcel
    vx
    cX
    c0
    cB
    vk
    cprod
    #
    cmpt
    #
    @3
    wcel
    vx
    cX
    vz
    cv
    #
    cB
    vk
    cprod
    #
    cmpt
    #
    @3
    wcel
    #
    vx
    cX
    @6
    vw
    cv
    #
    csn
    cun
    #
    cB
    vk
    cprod
    #
    cmpt
    #
    @3
    wcel
    #
    vx
    cX
    cA
    cB
    vk
    cprod
    #
    cmpt
    #
    @3
    wcel
    vy
    vz
    vw
    cA
    @0
    c0
    wceq
    #
    @2
    @5
    @3
    @17
    vx
    cX
    @1
    @4
    @0
    c0
    cB
    vk
    prodeq1
    mpteq2dv
    eleq1d
    @0
    @6
    wceq
    #
    @2
    @8
    @3
    @18
    vx
    cX
    @1
    @7
    @0
    @6
    cB
    vk
    prodeq1
    mpteq2dv
    eleq1d
    @0
    @11
    wceq
    #
    @2
    @13
    @3
    @19
    vx
    cX
    @1
    @12
    @0
    @11
    cB
    vk
    prodeq1
    mpteq2dv
    eleq1d
    @0
    cA
    wceq
    #
    @2
    @16
    @3
    @20
    vx
    cX
    @1
    @15
    @0
    cA
    cB
    vk
    prodeq1
    mpteq2dv
    eleq1d
    wph
    @5
    vy
    cX
    c1
    cmpt
    #
    @3
    @5
    @21
    wceq
    wph
    @5
    vx
    cX
    c1
    cmpt
    @21
    vx
    cX
    @4
    c1
    cB
    vk
    prod0
    mpteq2i
    vx
    vy
    cX
    c1
    c1
    vx
    cv
    @0
    wceq
    #
    c1
    eqidd
    cbvmptv
    eqtri
    a1i
    wph
    vy
    c1
    cJ
    cK
    cX
    cc
    fprodcn.j
    cK
    cc
    ctopon
    cfv
    wcel
    wph
    cK
    fprodcn.k
    cnfldtopon
    a1i
    wph
    1cnd
    cnmptc
    eqeltrd
    wph
    @6
    cA
    wss
    #
    @10
    cA
    @6
    cdif
    wcel
    #
    wa
    #
    wa
    #
    @9
    @14
    @26
    @9
    wa
    #
    @13
    vy
    cX
    @11
    vx
    @0
    cB
    csb
    #
    vk
    cprod
    #
    cmpt
    #
    @3
    @13
    @30
    wceq
    @27
    vx
    vy
    cX
    @12
    @29
    vy
    @12
    nfcv
    vx
    @11
    @28
    vk
    vx
    @11
    nfcv
    vx
    @0
    cB
    nfcsb1v
    #
    nfcprod
    @22
    @11
    cB
    @28
    vk
    vx
    @0
    cB
    csbeq1a
    #
    prodeq2ad
    cbvmpt
    a1i
    @27
    vy
    cA
    @28
    vk
    cJ
    cK
    @10
    cX
    @6
    @26
    @9
    vk
    wph
    @25
    vk
    fprodcn.d
    @25
    vk
    nfv
    nfan
    vk
    @8
    @3
    vk
    vx
    cX
    @7
    vk
    cX
    nfcv
    @6
    cB
    vk
    vk
    @6
    nfcv
    nfcprod1
    nfmpt
    vk
    @3
    nfcv
    nfel
    nfan
    fprodcn.k
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    @25
    @9
    fprodcn.j
    ad2antrr
    wph
    cA
    cfn
    wcel
    @25
    @9
    fprodcn.a
    ad2antrr
    wph
    vk
    cv
    cA
    wcel
    #
    vy
    cX
    @28
    cmpt
    #
    @3
    wcel
    @25
    @9
    wph
    @33
    wa
    #
    @34
    vx
    cX
    cB
    cmpt
    #
    @3
    @34
    @36
    wceq
    @35
    @36
    @34
    vx
    vy
    cX
    cB
    @28
    vy
    cB
    nfcv
    @31
    @32
    cbvmpt
    eqcomi
    a1i
    fprodcn.b
    eqeltrd
    ad4ant14
    wph
    @23
    @24
    @9
    simplrl
    wph
    @23
    @24
    @9
    simplrr
    @9
    vy
    cX
    @6
    @28
    vk
    cprod
    #
    cmpt
    #
    @3
    wcel
    #
    @26
    @9
    @39
    @8
    @38
    @3
    vx
    vy
    cX
    @7
    @37
    vy
    @7
    nfcv
    vx
    @6
    @28
    vk
    vx
    @6
    nfcv
    @31
    nfcprod
    @22
    @6
    cB
    @28
    vk
    @32
    prodeq2sdv
    cbvmpt
    eleq1i
    biimpi
    adantl
    fprodcnlem
    eqeltrd
    ex
    fprodcn.a
    findcard2d
end
