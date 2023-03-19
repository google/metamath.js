include "ccxp.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "crli.mm"
include "wbr.mm"
include "cv.mm"
include "cle.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "c1.mm"
include "cdiv.mm"
include "cc.mm"
include "wf.mm"
include "cdm.mm"
include "rlimf.mm"
include "syl.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "feq2d.mm"
include "mpbid.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "adantr.mm"
include "simpr.mm"
include "rprecred.mm"
include "rpcxpcld.mm"
include "rlimi.mm"
include "rlimmptrcl.mm"
include "adantlr.mm"
include "abscld.mm"
include "absge0d.mm"
include "rpred.mm"
include "rpge0d.mm"
include "ad2antrr.mm"
include "cxplt2d.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "abscxp2.mm"
include "syl2anc.mm"
include "cmul.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "recid2d.mm"
include "oveq2d.mm"
include "simplr.mm"
include "cxpmuld.mm"
include "cxp1d.mm"
include "3eqtr3rd.mm"
include "breq12d.mm"
include "3bitr4d.mm"
include "biimpd.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdv.mm"
include "mpd.mm"
include "cxpcld.mm"
include "wss.mm"
include "rlimss.mm"
include "eqsstr3d.mm"
include "rlim0.mm"
include "mpbird.mm"

theorem rlimcxp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vn: setvar n
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume rlimcxp.1: |- ( ( ph /\ n e. A ) -> B e. V )
  assume rlimcxp.2: |- ( ph -> ( n e. A |-> B ) ~~>r 0 )
  assume rlimcxp.3: |- ( ph -> C e. RR+ )

  disjoint A n
  disjoint C n
  disjoint n ph
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( n e. A |-> ( B ^c C ) ) ~~>r 0 )

  proof
    wph
    vn
    cA
    cB
    cC
    ccxp
    co
    #
    cmpt
    cc0
    crli
    wbr
    vy
    cv
    vn
    cv
    #
    cle
    wbr
    #
    @0
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wi
    #
    vn
    cA
    wral
    #
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    wph
    @8
    vx
    crp
    wph
    @4
    crp
    wcel
    #
    wa
    #
    @2
    cB
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    c1
    cC
    cdiv
    co
    #
    ccxp
    co
    #
    clt
    wbr
    #
    wi
    #
    vn
    cA
    wral
    #
    vy
    cr
    wrex
    @8
    @10
    vy
    vn
    cA
    cB
    cc0
    @14
    cc
    wph
    cB
    cc
    wcel
    #
    vn
    cA
    wral
    #
    @9
    wph
    cA
    cc
    vn
    cA
    cB
    cmpt
    #
    wf
    #
    @19
    wph
    @20
    cdm
    #
    cc
    @20
    wf
    #
    @21
    wph
    @20
    cc0
    crli
    wbr
    #
    @23
    rlimcxp.2
    cc0
    @20
    rlimf
    syl
    wph
    @22
    cA
    cc
    @20
    wph
    cB
    cV
    wcel
    #
    vn
    cA
    wral
    @22
    cA
    wceq
    wph
    @25
    vn
    cA
    rlimcxp.1
    ralrimiva
    vn
    cA
    cB
    cV
    dmmptg
    syl
    #
    feq2d
    mpbid
    vn
    cA
    cc
    cB
    @20
    @20
    eqid
    fmpt
    sylibr
    adantr
    @10
    @4
    @13
    wph
    @9
    simpr
    @10
    cC
    wph
    cC
    crp
    wcel
    #
    @9
    rlimcxp.3
    adantr
    rprecred
    #
    rpcxpcld
    #
    wph
    @24
    @9
    rlimcxp.2
    adantr
    rlimi
    @10
    @17
    @7
    vy
    cr
    @10
    @16
    @6
    vn
    cA
    @10
    @1
    cA
    wcel
    #
    wa
    #
    @15
    @5
    @2
    @31
    @15
    @5
    @31
    cB
    cabs
    cfv
    #
    @14
    clt
    wbr
    @32
    cC
    ccxp
    co
    #
    @14
    cC
    ccxp
    co
    #
    clt
    wbr
    @15
    @5
    @31
    @32
    @14
    cC
    @31
    cB
    wph
    @30
    @18
    @9
    wph
    cA
    cB
    cc0
    vn
    cV
    rlimcxp.1
    rlimcxp.2
    rlimmptrcl
    #
    adantlr
    #
    abscld
    @31
    cB
    @36
    absge0d
    @31
    @14
    @10
    @14
    crp
    wcel
    @30
    @29
    adantr
    #
    rpred
    @31
    @14
    @37
    rpge0d
    wph
    @27
    @9
    @30
    rlimcxp.3
    ad2antrr
    #
    cxplt2d
    @31
    @12
    @32
    @14
    clt
    @31
    @11
    cB
    cabs
    @31
    cB
    @36
    subid1d
    fveq2d
    breq1d
    @31
    @3
    @33
    @4
    @34
    clt
    @31
    @18
    cC
    cr
    wcel
    @3
    @33
    wceq
    @36
    @31
    cC
    @38
    rpred
    cB
    cC
    abscxp2
    syl2anc
    @31
    @4
    @13
    cC
    cmul
    co
    #
    ccxp
    co
    @4
    c1
    ccxp
    co
    @34
    @4
    @31
    @39
    c1
    @4
    ccxp
    @31
    cC
    @31
    cC
    @38
    rpcnd
    #
    @31
    cC
    @38
    rpne0d
    recid2d
    oveq2d
    @31
    @4
    @13
    cC
    wph
    @9
    @30
    simplr
    #
    @10
    @13
    cr
    wcel
    @30
    @28
    adantr
    @40
    cxpmuld
    @31
    @4
    @31
    @4
    @41
    rpcnd
    cxp1d
    3eqtr3rd
    breq12d
    3bitr4d
    biimpd
    imim2d
    ralimdva
    reximdv
    mpd
    ralrimiva
    wph
    vx
    vy
    vn
    cA
    @0
    wph
    @0
    cc
    wcel
    vn
    cA
    wph
    @30
    wa
    cB
    cC
    @35
    wph
    cC
    cc
    wcel
    @30
    wph
    cC
    rlimcxp.3
    rpcnd
    adantr
    cxpcld
    ralrimiva
    wph
    cA
    @22
    cr
    @26
    wph
    @24
    @22
    cr
    wss
    rlimcxp.2
    cc0
    @20
    rlimss
    syl
    eqsstr3d
    rlim0
    mpbird
end
