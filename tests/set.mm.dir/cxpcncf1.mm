include "cc.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "co.mm"
include "cdif.mm"
include "cv.mm"
include "ccxp.mm"
include "cmpt.mm"
include "cres.mm"
include "ccncf.mm"
include "wss.mm"
include "wceq.mm"
include "resmpt.mm"
include "syl.mm"
include "wcel.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "ccn.mm"
include "ctopon.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "difss.mm"
include "resttopon.mm"
include "mp2an.mm"
include "a1i.mm"
include "cnmptid.mm"
include "cnmptc.mm"
include "cmpt2.mm"
include "ctx.mm"
include "cxpcn.mm"
include "oveq12.mm"
include "cnmpt12.mm"
include "ssid.mm"
include "cvv.mm"
include "elexi.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "eleqtrd.mm"
include "rescncf.mm"
include "imp.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem cxpcncf1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cD: class D
  let vy: setvar y
  let vz: setvar z
  assume cxpcncf1.a: |- ( ph -> A e. CC )
  assume cxpcncf1.d: |- ( ph -> D C_ ( CC \ ( -oo (,] 0 ) ) )

  disjoint A x
  disjoint D x
  disjoint ph x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( ph -> ( x e. D |-> ( x ^c A ) ) e. ( D -cn-> CC ) )

  proof
    wph
    vx
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    #
    vx
    cv
    #
    cA
    ccxp
    co
    #
    cmpt
    #
    cD
    cres
    #
    vx
    cD
    @3
    cmpt
    #
    cD
    cc
    ccncf
    co
    #
    wph
    cD
    @1
    wss
    #
    @5
    @6
    wceq
    cxpcncf1.d
    vx
    @1
    cD
    @3
    resmpt
    syl
    wph
    @8
    @4
    @1
    cc
    ccncf
    co
    #
    wcel
    #
    @5
    @7
    wcel
    #
    cxpcncf1.d
    wph
    @4
    ccnfld
    ctopn
    cfv
    #
    @1
    crest
    co
    #
    @12
    ccn
    co
    #
    @9
    wph
    vx
    vy
    vz
    @2
    cA
    vy
    cv
    #
    vz
    cv
    #
    ccxp
    co
    #
    @3
    @13
    @13
    @12
    @12
    @1
    @1
    cc
    @13
    @1
    ctopon
    cfv
    wcel
    #
    wph
    @12
    cc
    ctopon
    cfv
    #
    wcel
    #
    @1
    cc
    wss
    #
    @18
    @12
    @12
    eqid
    #
    cnfldtopon
    #
    cc
    @0
    difss
    #
    @1
    @12
    cc
    resttopon
    mp2an
    a1i
    #
    wph
    vx
    @13
    @1
    @25
    cnmptid
    wph
    vx
    cA
    @13
    @12
    @1
    cc
    @25
    @20
    wph
    @23
    a1i
    #
    cxpcncf1.a
    cnmptc
    @25
    @26
    vy
    vz
    @1
    cc
    @17
    cmpt2
    @13
    @12
    ctx
    co
    @12
    ccn
    co
    wcel
    wph
    vy
    vz
    @1
    @12
    @13
    @1
    eqid
    @22
    @13
    eqid
    #
    cxpcn
    a1i
    @15
    @2
    @16
    cA
    ccxp
    oveq12
    cnmpt12
    @14
    @9
    wceq
    wph
    @9
    @14
    @21
    cc
    cc
    wss
    @9
    @14
    wceq
    @24
    cc
    ssid
    @1
    cc
    @12
    @13
    @12
    @22
    @27
    @12
    cc
    crest
    co
    #
    @12
    @12
    cvv
    wcel
    @28
    @12
    wceq
    @12
    @19
    @23
    elexi
    @12
    cvv
    cc
    cc
    @12
    @23
    toponunii
    restid
    ax-mp
    eqcomi
    cncfcn
    mp2an
    eqcomi
    a1i
    eleqtrd
    @8
    @10
    @11
    @1
    cc
    cD
    @4
    rescncf
    imp
    syl2anc
    eqeltrrd
end
