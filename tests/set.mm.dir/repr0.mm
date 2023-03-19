include "cc0.mm"
include "crepr.mm"
include "cfv.mm"
include "co.mm"
include "cfzo.mm"
include "cv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "c0.mm"
include "csn.mm"
include "cif.mm"
include "cn0.mm"
include "wcel.mm"
include "0nn0.mm"
include "a1i.mm"
include "reprval.mm"
include "wa.mm"
include "wb.mm"
include "fzo0.mm"
include "sumeq1i.mm"
include "sum0.mm"
include "eqtri.mm"
include "eqeq1i.mm"
include "0ex.mm"
include "snid.mm"
include "cvv.mm"
include "cn.mm"
include "nnex.mm"
include "ssexd.mm"
include "mapdm0.mm"
include "syl.mm"
include "syl5eleqr.mm"
include "oveq2i.mm"
include "syl6eleqr.mm"
include "adantr.mm"
include "simpr.mm"
include "eqcomd.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "elsni.mm"
include "ad4ant13.mm"
include "rabeqsnd.mm"
include "wn.mm"
include "wral.mm"
include "simplr.mm"
include "neqned.mm"
include "necomd.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "ifeqda.mm"
include "eqtr4d.mm"

theorem repr0
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cM: class M
  let vb: setvar b
  let vc: setvar c
  let vm: setvar m
  let va: setvar a
  let vs: setvar s
  assume reprval.a: |- ( ph -> A C_ NN )
  assume reprval.m: |- ( ph -> M e. ZZ )
  assume reprval.s: |- ( ph -> S e. NN0 )


  assert |- ( ph -> ( A ( repr ` 0 ) M ) = if ( M = 0 , { (/) } , (/) ) )

  proof
    wph
    cA
    cM
    cc0
    crepr
    cfv
    co
    cc0
    cc0
    cfzo
    co
    #
    va
    cv
    vc
    cv
    #
    cfv
    #
    va
    csu
    #
    cM
    wceq
    #
    vc
    cA
    @0
    cmap
    co
    #
    crab
    #
    cM
    cc0
    wceq
    #
    c0
    csn
    #
    c0
    cif
    wph
    cA
    cc0
    cM
    va
    vc
    reprval.a
    reprval.m
    cc0
    cn0
    wcel
    wph
    0nn0
    a1i
    reprval
    wph
    @7
    @8
    c0
    @6
    wph
    @7
    wa
    #
    @6
    @8
    @9
    @4
    cc0
    cM
    wceq
    #
    vc
    @5
    c0
    @4
    @10
    wb
    @1
    c0
    wceq
    #
    @3
    cc0
    cM
    @3
    c0
    @2
    va
    csu
    cc0
    @0
    c0
    @2
    va
    cc0
    fzo0
    #
    sumeq1i
    @2
    va
    sum0
    eqtri
    #
    eqeq1i
    a1i
    wph
    c0
    @5
    wcel
    @7
    wph
    c0
    cA
    c0
    cmap
    co
    #
    @5
    wph
    c0
    @8
    @14
    c0
    0ex
    snid
    wph
    cA
    cvv
    wcel
    @14
    @8
    wceq
    wph
    cA
    cn
    cvv
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    reprval.a
    ssexd
    cA
    cvv
    mapdm0
    syl
    #
    syl5eleqr
    @0
    c0
    cA
    cmap
    @12
    oveq2i
    #
    syl6eleqr
    adantr
    @9
    cM
    cc0
    wph
    @7
    simpr
    eqcomd
    wph
    @1
    @5
    wcel
    #
    @11
    @7
    @4
    wph
    @17
    wa
    @1
    @8
    wcel
    #
    @11
    wph
    @17
    @18
    wph
    @5
    @8
    @1
    wph
    @5
    @14
    @8
    @16
    @15
    syl5eq
    eleq2d
    biimpa
    @1
    c0
    elsni
    syl
    ad4ant13
    rabeqsnd
    eqcomd
    wph
    @7
    wn
    #
    wa
    #
    @6
    c0
    @20
    @4
    wn
    #
    vc
    @5
    wral
    @6
    c0
    wceq
    @20
    @21
    vc
    @5
    @20
    @17
    wa
    #
    @3
    cM
    @22
    @3
    cc0
    cM
    @3
    cc0
    wceq
    @22
    @13
    a1i
    @22
    cM
    cc0
    @22
    cM
    cc0
    wph
    @19
    @17
    simplr
    neqned
    necomd
    eqnetrd
    neneqd
    ralrimiva
    @4
    vc
    @5
    rabeq0
    sylibr
    eqcomd
    ifeqda
    eqtr4d
end
