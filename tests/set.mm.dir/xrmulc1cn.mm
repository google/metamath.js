include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "ccn.mm"
include "co.mm"
include "ctsr.mm"
include "wcel.mm"
include "cxr.mm"
include "wiso.mm"
include "letsr.mm"
include "a1i.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "cxmu.mm"
include "wceq.mm"
include "wreu.mm"
include "wa.mm"
include "simpr.mm"
include "crp.mm"
include "adantr.mm"
include "rpxrd.mm"
include "xmulcld.mm"
include "ralrimiva.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "rpred.mm"
include "rpne0d.mm"
include "xreceu.mm"
include "syl3anc.mm"
include "eqcom.mm"
include "adantlr.mm"
include "xmulcom.mm"
include "syl2anc.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "reubidva.mm"
include "mpbird.mm"
include "f1ompt.mm"
include "sylanbrc.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "xlemul1.mm"
include "cvv.mm"
include "ovex.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "oveq1.mm"
include "fvmpt.mm"
include "adantl.mm"
include "breq12d.mm"
include "bitr4d.mm"
include "df-isom.mm"
include "ledm.mm"
include "ordthmeolem.mm"
include "oveq12i.mm"
include "syl6eleqr.mm"

theorem xrmulc1cn
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cF: class F
  let cJ: class J
  let vy: setvar y
  assume xrmulc1cn.k: |- J = ( ordTop ` <_ )
  assume xrmulc1cn.f: |- F = ( x e. RR* |-> ( x *e C ) )
  assume xrmulc1cn.c: |- ( ph -> C e. RR+ )

  disjoint C x
  disjoint F x
  disjoint ph x
  disjoint x y
  disjoint C y
  disjoint F y
  disjoint ph y
  assert |- ( ph -> F e. ( J Cn J ) )

  proof
    wph
    cF
    cle
    cordt
    cfv
    #
    @0
    ccn
    co
    #
    cJ
    cJ
    ccn
    co
    wph
    cle
    ctsr
    wcel
    #
    @2
    cxr
    cxr
    cle
    cle
    cF
    wiso
    #
    cF
    @1
    wcel
    @2
    wph
    letsr
    a1i
    #
    @4
    wph
    cxr
    cxr
    cF
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    @6
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    cle
    wbr
    #
    wb
    #
    vy
    cxr
    wral
    #
    vx
    cxr
    wral
    @3
    wph
    @6
    cC
    cxmu
    co
    #
    cxr
    wcel
    #
    vx
    cxr
    wral
    @7
    @14
    wceq
    #
    vx
    cxr
    wreu
    #
    vy
    cxr
    wral
    @5
    wph
    @15
    vx
    cxr
    wph
    @6
    cxr
    wcel
    #
    wa
    #
    @6
    cC
    wph
    @18
    simpr
    @19
    cC
    wph
    cC
    crp
    wcel
    #
    @18
    xrmulc1cn.c
    adantr
    rpxrd
    #
    xmulcld
    ralrimiva
    wph
    @17
    vy
    cxr
    wph
    @7
    cxr
    wcel
    #
    wa
    #
    @17
    cC
    @6
    cxmu
    co
    #
    @7
    wceq
    #
    vx
    cxr
    wreu
    #
    @23
    @22
    cC
    cr
    wcel
    cC
    cc0
    wne
    @26
    wph
    @22
    simpr
    @23
    cC
    wph
    @20
    @22
    xrmulc1cn.c
    adantr
    #
    rpred
    @23
    cC
    @27
    rpne0d
    vx
    @7
    cC
    xreceu
    syl3anc
    @23
    @16
    @25
    vx
    cxr
    @16
    @14
    @7
    wceq
    @23
    @18
    wa
    #
    @25
    @7
    @14
    eqcom
    @28
    @14
    @24
    @7
    @28
    @18
    cC
    cxr
    wcel
    #
    @14
    @24
    wceq
    @23
    @18
    simpr
    wph
    @18
    @29
    @22
    @21
    adantlr
    @6
    cC
    xmulcom
    syl2anc
    eqeq1d
    syl5bb
    reubidva
    mpbird
    ralrimiva
    vx
    vy
    cxr
    cxr
    @14
    cF
    xrmulc1cn.f
    f1ompt
    sylanbrc
    wph
    @13
    vx
    cxr
    @19
    @12
    vy
    cxr
    @19
    @22
    wa
    #
    @8
    @14
    @7
    cC
    cxmu
    co
    #
    cle
    wbr
    #
    @11
    @30
    @18
    @22
    @20
    @8
    @32
    wb
    wph
    @18
    @22
    simplr
    #
    @19
    @22
    simpr
    wph
    @20
    @18
    @22
    xrmulc1cn.c
    ad2antrr
    @6
    @7
    cC
    xlemul1
    syl3anc
    @30
    @9
    @14
    @10
    @31
    cle
    @30
    @18
    @14
    cvv
    wcel
    @9
    @14
    wceq
    @33
    @6
    cC
    cxmu
    ovex
    vx
    cxr
    @14
    cvv
    cF
    xrmulc1cn.f
    fvmpt2
    sylancl
    @22
    @10
    @31
    wceq
    @19
    vx
    @7
    @14
    @31
    cxr
    cF
    @6
    @7
    cC
    cxmu
    oveq1
    xrmulc1cn.f
    @7
    cC
    cxmu
    ovex
    fvmpt
    adantl
    breq12d
    bitr4d
    ralrimiva
    ralrimiva
    vx
    vy
    cxr
    cxr
    cle
    cle
    cF
    df-isom
    sylanbrc
    cle
    cle
    cF
    ctsr
    ctsr
    cxr
    cxr
    ledm
    ledm
    ordthmeolem
    syl3anc
    cJ
    @0
    cJ
    @0
    ccn
    xrmulc1cn.k
    xrmulc1cn.k
    oveq12i
    syl6eleqr
end
