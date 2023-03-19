include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "c2o.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "cixp.mm"
include "wcel.mm"
include "wfn.mm"
include "cfv.mm"
include "c1o.mm"
include "w3a.mm"
include "wa.mm"
include "xpsfrnel.mm"
include "cvv.mm"
include "cxp.mm"
include "cdm.mm"
include "cun.mm"
include "cpr.mm"
include "0ex.mm"
include "prid1.mm"
include "df2o3.mm"
include "eleqtrri.mm"
include "fndm.mm"
include "syl5eleqr.mm"
include "xpsc.mm"
include "dmeqi.mm"
include "dmun.mm"
include "eqtri.mm"
include "syl6eleq.mm"
include "wo.mm"
include "elun.mm"
include "wbr.mm"
include "wex.mm"
include "eldm.mm"
include "brxp.mm"
include "elsni.mm"
include "vex.mm"
include "syl6eqelr.mm"
include "adantl.mm"
include "sylbi.mm"
include "exlimiv.mm"
include "dmxpss.mm"
include "sseli.mm"
include "1n0.mm"
include "neii.mm"
include "pm2.21i.mm"
include "eqcoms.mm"
include "3syl.mm"
include "jaoi.mm"
include "syl.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "prid2.mm"
include "jca.mm"
include "3ad2ant1.mm"
include "elex.mm"
include "anim12i.mm"
include "3anass.mm"
include "xpscfn.mm"
include "biantrurd.mm"
include "xpsc0.mm"
include "eleq1d.mm"
include "xpsc1.mm"
include "bi2anan9.mm"
include "bitr3d.mm"
include "syl5bb.mm"
include "pm5.21nii.mm"
include "bitri.mm"

theorem xpsfrnel2
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cX: class X
  let cY: class Y
  let cG: class G

  disjoint A k
  disjoint B k
  disjoint X k
  disjoint Y k
  disjoint G k
  assert |- ( `' ( { X } +c { Y } ) e. X_ k e. 2o if ( k = (/) , A , B ) <-> ( X e. A /\ Y e. B ) )

  proof
    cX
    csn
    #
    cY
    csn
    #
    ccda
    co
    ccnv
    #
    vk
    c2o
    vk
    cv
    #
    c0
    wceq
    cA
    cB
    cif
    cixp
    wcel
    @2
    c2o
    wfn
    #
    c0
    @2
    cfv
    #
    cA
    wcel
    #
    c1o
    @2
    cfv
    #
    cB
    wcel
    #
    w3a
    #
    cX
    cA
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cA
    cB
    vk
    @2
    xpsfrnel
    @9
    cX
    cvv
    wcel
    #
    cY
    cvv
    wcel
    #
    wa
    #
    @12
    @4
    @6
    @15
    @8
    @4
    @13
    @14
    @4
    c0
    c0
    csn
    #
    @0
    cxp
    #
    cdm
    #
    c1o
    csn
    #
    @1
    cxp
    #
    cdm
    #
    cun
    #
    wcel
    #
    @13
    @4
    c0
    @2
    cdm
    #
    @22
    @4
    c0
    c2o
    @24
    c0
    c0
    c1o
    cpr
    #
    c2o
    c0
    c1o
    0ex
    prid1
    df2o3
    eleqtrri
    c2o
    @2
    fndm
    #
    syl5eleqr
    @24
    @17
    @20
    cun
    #
    cdm
    @22
    @2
    @27
    cX
    cY
    xpsc
    dmeqi
    @17
    @20
    dmun
    eqtri
    #
    syl6eleq
    @23
    c0
    @18
    wcel
    #
    c0
    @21
    wcel
    #
    wo
    @13
    c0
    @18
    @21
    elun
    @29
    @13
    @30
    @29
    c0
    @3
    @17
    wbr
    #
    vk
    wex
    @13
    vk
    c0
    @17
    0ex
    eldm
    @31
    @13
    vk
    @31
    c0
    @16
    wcel
    #
    @3
    @0
    wcel
    #
    wa
    @13
    c0
    @3
    @16
    @0
    brxp
    @33
    @13
    @32
    @33
    cX
    @3
    cvv
    @3
    cX
    elsni
    vk
    vex
    #
    syl6eqelr
    adantl
    sylbi
    exlimiv
    sylbi
    @30
    c0
    @19
    wcel
    c0
    c1o
    wceq
    @13
    @21
    @19
    c0
    @19
    @1
    dmxpss
    sseli
    c0
    c1o
    elsni
    @13
    c1o
    c0
    c1o
    c0
    wceq
    #
    @13
    c1o
    c0
    1n0
    neii
    #
    pm2.21i
    eqcoms
    3syl
    jaoi
    sylbi
    syl
    @4
    c1o
    @22
    wcel
    #
    @14
    @4
    c1o
    @24
    @22
    @4
    c1o
    c2o
    @24
    c1o
    @25
    c2o
    c0
    c1o
    c1o
    con0
    1on
    elexi
    #
    prid2
    df2o3
    eleqtrri
    @26
    syl5eleqr
    @28
    syl6eleq
    @37
    c1o
    @18
    wcel
    #
    c1o
    @21
    wcel
    #
    wo
    @14
    c1o
    @18
    @21
    elun
    @39
    @14
    @40
    @39
    c1o
    @16
    wcel
    @35
    @14
    @18
    @16
    c1o
    @16
    @0
    dmxpss
    sseli
    c1o
    c0
    elsni
    @35
    @14
    @36
    pm2.21i
    3syl
    @40
    c1o
    @3
    @20
    wbr
    #
    vk
    wex
    @14
    vk
    c1o
    @20
    @38
    eldm
    @41
    @14
    vk
    @41
    c1o
    @19
    wcel
    #
    @3
    @1
    wcel
    #
    wa
    @14
    c1o
    @3
    @19
    @1
    brxp
    @43
    @14
    @42
    @43
    cY
    @3
    cvv
    @3
    cY
    elsni
    @34
    syl6eqelr
    adantl
    sylbi
    exlimiv
    sylbi
    jaoi
    sylbi
    syl
    jca
    3ad2ant1
    @10
    @13
    @11
    @14
    cX
    cA
    elex
    cY
    cB
    elex
    anim12i
    @9
    @4
    @6
    @8
    wa
    #
    wa
    #
    @15
    @12
    @4
    @6
    @8
    3anass
    @15
    @44
    @45
    @12
    @15
    @4
    @44
    cX
    cY
    cvv
    cvv
    xpscfn
    biantrurd
    @13
    @6
    @10
    @14
    @8
    @11
    @13
    @5
    cX
    cA
    cX
    cY
    cvv
    xpsc0
    eleq1d
    @14
    @7
    cY
    cB
    cX
    cY
    cvv
    xpsc1
    eleq1d
    bi2anan9
    bitr3d
    syl5bb
    pm5.21nii
    bitri
end
