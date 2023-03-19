include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "climc.mm"
include "wcel.mm"
include "cc0.mm"
include "cmin.mm"
include "cmpt.mm"
include "cmul.mm"
include "eqid.mm"
include "cv.mm"
include "wa.mm"
include "cc.mm"
include "limccl.mm"
include "sseldi.mm"
include "adantr.mm"
include "csn.mm"
include "eldifad.mm"
include "subcld.mm"
include "mulcld.mm"
include "wceq.mm"
include "cdif.mm"
include "wne.mm"
include "eldifsni.mm"
include "syl.mm"
include "mulne0d.mm"
include "neneqd.mm"
include "wb.mm"
include "elsng.mm"
include "mtbird.mm"
include "eldifd.mm"
include "cneg.mm"
include "caddc.mm"
include "negcld.mm"
include "limcmptdm.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "w3a.mm"
include "limcrcl.mm"
include "simp3d.mm"
include "constlimc.mm"
include "neglimc.mm"
include "addlimc.mm"
include "negidd.mm"
include "negsubd.mm"
include "mpteq2dva.mm"
include "oveq1d.mm"
include "3eltr3d.mm"
include "mullimc.mm"
include "0ellimcdiv.mm"
include "1cnd.mm"
include "divsubdivd.mm"
include "mulid2d.mm"
include "oveq12d.mm"
include "eqtr2d.mm"
include "eleqtrd.mm"
include "reccld.mm"
include "ellimcabssub0.mm"
include "mpbird.mm"

theorem reclimc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  assume reclimc.f: |- F = ( x e. A |-> B )
  assume reclimc.g: |- G = ( x e. A |-> ( 1 / B ) )
  assume reclimc.b: |- ( ( ph /\ x e. A ) -> B e. ( CC \ { 0 } ) )
  assume reclimc.c: |- ( ph -> C e. ( F limCC D ) )
  assume reclimc.cne0: |- ( ph -> C =/= 0 )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint ph x
  assert |- ( ph -> ( 1 / C ) e. ( G limCC D ) )

  proof
    wph
    c1
    cC
    cdiv
    co
    #
    cG
    cD
    climc
    co
    wcel
    cc0
    vx
    cA
    c1
    cB
    cdiv
    co
    #
    @0
    cmin
    co
    #
    cmpt
    #
    cD
    climc
    co
    #
    wcel
    wph
    cc0
    vx
    cA
    cC
    cB
    cmin
    co
    #
    cB
    cC
    cmul
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cD
    climc
    co
    @4
    wph
    vx
    cA
    @5
    @6
    cC
    cC
    cmul
    co
    cD
    vx
    cA
    @5
    cmpt
    #
    vx
    cA
    @6
    cmpt
    #
    @8
    @9
    eqid
    @10
    eqid
    #
    @8
    eqid
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    cC
    cB
    wph
    cC
    cc
    wcel
    @12
    wph
    cF
    cD
    climc
    co
    #
    cc
    cC
    cD
    cF
    limccl
    reclimc.c
    sseldi
    #
    adantr
    #
    @13
    cB
    cc
    cc0
    csn
    #
    reclimc.b
    eldifad
    #
    subcld
    @13
    @6
    cc
    @17
    @13
    cB
    cC
    @18
    @16
    mulcld
    #
    @13
    @6
    @17
    wcel
    #
    @6
    cc0
    wceq
    #
    @13
    @6
    cc0
    @13
    cB
    cC
    @18
    @16
    @13
    cB
    cc
    @17
    cdif
    wcel
    cB
    cc0
    wne
    reclimc.b
    cB
    cc
    cc0
    eldifsni
    syl
    #
    wph
    cC
    cc0
    wne
    @12
    reclimc.cne0
    adantr
    #
    mulne0d
    neneqd
    @13
    @6
    cc
    wcel
    @20
    @21
    wb
    @19
    @6
    cc0
    cc
    elsng
    syl
    mtbird
    eldifd
    wph
    cC
    cC
    cneg
    #
    caddc
    co
    vx
    cA
    cC
    cB
    cneg
    #
    caddc
    co
    #
    cmpt
    #
    cD
    climc
    co
    cc0
    @9
    cD
    climc
    co
    wph
    vx
    cA
    cC
    @25
    cD
    cC
    vx
    cA
    cC
    cmpt
    #
    vx
    cA
    @25
    cmpt
    #
    @27
    @24
    @28
    eqid
    #
    @29
    eqid
    #
    @27
    eqid
    @16
    @13
    cB
    @18
    negcld
    wph
    vx
    cA
    cC
    cD
    @28
    @30
    wph
    vx
    cA
    cB
    cC
    cD
    cF
    reclimc.f
    @18
    reclimc.c
    limcmptdm
    #
    @15
    wph
    cF
    cdm
    #
    cc
    cF
    wf
    #
    @33
    cc
    wss
    #
    cD
    cc
    wcel
    #
    wph
    cC
    @14
    wcel
    @34
    @35
    @36
    w3a
    reclimc.c
    cD
    cC
    cF
    limcrcl
    syl
    simp3d
    #
    constlimc
    #
    wph
    vx
    cA
    cB
    cC
    cD
    cF
    @29
    reclimc.f
    @31
    @18
    reclimc.c
    neglimc
    addlimc
    wph
    cC
    @15
    negidd
    wph
    @27
    @9
    cD
    climc
    wph
    vx
    cA
    @26
    @5
    @13
    cC
    cB
    @16
    @18
    negsubd
    mpteq2dva
    oveq1d
    3eltr3d
    wph
    vx
    cA
    cB
    cC
    cD
    cF
    @28
    @10
    cC
    cC
    reclimc.f
    @30
    @11
    @18
    @16
    reclimc.c
    @38
    mullimc
    wph
    cC
    cC
    @15
    @15
    reclimc.cne0
    reclimc.cne0
    mulne0d
    0ellimcdiv
    wph
    @8
    @3
    cD
    climc
    wph
    vx
    cA
    @7
    @2
    @13
    @2
    c1
    cC
    cmul
    co
    #
    c1
    cB
    cmul
    co
    #
    cmin
    co
    #
    @6
    cdiv
    co
    @7
    @13
    c1
    cB
    c1
    cC
    @13
    1cnd
    #
    @18
    @42
    @16
    @22
    @23
    divsubdivd
    @13
    @41
    @5
    @6
    cdiv
    @13
    @39
    cC
    @40
    cB
    cmin
    @13
    cC
    @16
    mulid2d
    @13
    cB
    @18
    mulid2d
    oveq12d
    oveq1d
    eqtr2d
    mpteq2dva
    oveq1d
    eleqtrd
    wph
    vx
    cA
    @1
    @0
    cD
    cG
    @3
    reclimc.g
    @3
    eqid
    @32
    @13
    cB
    @18
    @22
    reccld
    @37
    wph
    cC
    @15
    reclimc.cne0
    reccld
    ellimcabssub0
    mpbird
end
