include "c0.mm"
include "wceq.mm"
include "csn.mm"
include "cvoln.mm"
include "cfv.mm"
include "cc0.mm"
include "wa.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "adantl.mm"
include "cfn.mm"
include "wcel.mm"
include "0fin.mm"
include "a1i.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "adantr.mm"
include "oveq2.mm"
include "eleqtrd.mm"
include "snvonmbl.mm"
include "von0val.mm"
include "eqtrd.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "cv.mm"
include "cicc.mm"
include "cixp.mm"
include "cvol.mm"
include "cprod.mm"
include "rrxsnicc.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "simpr.mm"
include "wf.mm"
include "elmapi.mm"
include "syl.mm"
include "eqid.mm"
include "vonn0icc.mm"
include "chash.mm"
include "cexp.mm"
include "cxr.mm"
include "ffvelrnda.mm"
include "rexrd.mm"
include "iccid.mm"
include "volsn.mm"
include "prodeq2dv.mm"
include "cc.mm"
include "0cnd.mm"
include "fprodconst.mm"
include "syl2anc.mm"
include "cn.mm"
include "wb.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "0exp.mm"
include "3eqtrd.mm"
include "syldan.mm"
include "pm2.61dan.mm"

theorem vonsn
  let wph: wff ph
  let cA: class A
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume vonsn.1: |- ( ph -> X e. Fin )
  assume vonsn.2: |- ( ph -> A e. ( RR ^m X ) )


  assert |- ( ph -> ( ( voln ` X ) ` { A } ) = 0 )

  proof
    wph
    cX
    c0
    wceq
    #
    cA
    csn
    #
    cX
    cvoln
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    wph
    @0
    wa
    #
    @3
    @1
    c0
    cvoln
    cfv
    #
    cfv
    #
    cc0
    @0
    @3
    @7
    wceq
    wph
    @0
    @1
    @2
    @6
    cX
    c0
    cvoln
    fveq2
    fveq1d
    adantl
    @5
    @1
    @5
    cA
    c0
    c0
    cfn
    wcel
    @5
    0fin
    a1i
    @5
    cA
    cr
    cX
    cmap
    co
    #
    cr
    c0
    cmap
    co
    #
    wph
    cA
    @8
    wcel
    #
    @0
    vonsn.2
    adantr
    @0
    @8
    @9
    wceq
    wph
    cX
    c0
    cr
    cmap
    oveq2
    adantl
    eleqtrd
    snvonmbl
    von0val
    eqtrd
    wph
    @0
    wn
    #
    cX
    c0
    wne
    #
    @4
    @11
    @12
    wph
    cX
    c0
    neqne
    adantl
    wph
    @12
    wa
    #
    @3
    vk
    cX
    vk
    cv
    #
    cA
    cfv
    #
    @15
    cicc
    co
    #
    cixp
    #
    @2
    cfv
    #
    cX
    @16
    cvol
    cfv
    #
    vk
    cprod
    #
    cc0
    wph
    @3
    @18
    wceq
    @12
    wph
    @1
    @17
    @2
    wph
    @17
    @1
    wph
    cA
    vk
    cX
    vonsn.2
    rrxsnicc
    eqcomd
    fveq2d
    adantr
    @13
    cA
    cA
    vk
    @17
    cX
    wph
    cX
    cfn
    wcel
    #
    @12
    vonsn.1
    adantr
    wph
    @12
    simpr
    #
    wph
    cX
    cr
    cA
    wf
    #
    @12
    wph
    @10
    @23
    vonsn.2
    cA
    cr
    cX
    elmapi
    syl
    #
    adantr
    #
    @25
    @17
    eqid
    vonn0icc
    @13
    @20
    cX
    cc0
    vk
    cprod
    #
    cc0
    cX
    chash
    cfv
    #
    cexp
    co
    #
    cc0
    wph
    @20
    @26
    wceq
    @12
    wph
    cX
    @19
    cc0
    vk
    wph
    @14
    cX
    wcel
    wa
    #
    @19
    @15
    csn
    #
    cvol
    cfv
    #
    cc0
    @29
    @16
    @30
    cvol
    @29
    @15
    cxr
    wcel
    @16
    @30
    wceq
    @29
    @15
    wph
    cX
    cr
    @14
    cA
    @24
    ffvelrnda
    #
    rexrd
    @15
    iccid
    syl
    fveq2d
    @29
    @15
    cr
    wcel
    @31
    cc0
    wceq
    @32
    @15
    volsn
    syl
    eqtrd
    prodeq2dv
    adantr
    wph
    @26
    @28
    wceq
    #
    @12
    wph
    @21
    cc0
    cc
    wcel
    @33
    vonsn.1
    wph
    0cnd
    cX
    cc0
    vk
    fprodconst
    syl2anc
    adantr
    @13
    @27
    cn
    wcel
    #
    @28
    cc0
    wceq
    @13
    @34
    @12
    @22
    wph
    @34
    @12
    wb
    #
    @12
    wph
    @21
    @35
    vonsn.1
    cX
    hashnncl
    syl
    adantr
    mpbird
    @27
    0exp
    syl
    3eqtrd
    3eqtrd
    syldan
    pm2.61dan
end
