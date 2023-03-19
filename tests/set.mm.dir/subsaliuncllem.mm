include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cin.mm"
include "wceq.mm"
include "wral.mm"
include "wrex.mm"
include "ccom.mm"
include "wf.mm"
include "crn.mm"
include "wfn.mm"
include "wa.mm"
include "wss.mm"
include "crab.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "wi.mm"
include "id.mm"
include "ssrab2.mm"
include "a1i.mm"
include "eqsstrd.mm"
include "rexlimiv.mm"
include "mpd.mm"
include "adantl.mm"
include "r19.21bi.mm"
include "sseldd.mm"
include "ex.mm"
include "ralrimi.mm"
include "jca.mm"
include "ffnfv.mm"
include "sylibr.mm"
include "eqid.mm"
include "rabexd.mm"
include "ralrimivw.mm"
include "fnmpt.mm"
include "syl.mm"
include "dffn3.mm"
include "sylib.mm"
include "fco.mm"
include "syl2anc.mm"
include "nnex.mm"
include "elmapd.mm"
include "mpbird.mm"
include "syl5eqel.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "rspcva.mm"
include "wfun.mm"
include "ffund.mm"
include "cdm.mm"
include "simpr.mm"
include "cmpt.mm"
include "dmeqi.mm"
include "dmmptg.mm"
include "eqtrd.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "fvcod.mm"
include "fvmpt2d.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "elrab.mm"
include "simprd.mm"
include "ralrimiva.mm"
include "fveq1.mm"
include "ineq1d.mm"
include "ralbidv.mm"
include "rspcev.mm"

theorem subsaliuncllem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cS: class S
  let ve: setvar e
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let vk: setvar k
  assume subsaliuncllem.f: |- F/ y ph
  assume subsaliuncllem.s: |- ( ph -> S e. V )
  assume subsaliuncllem.g: |- G = ( n e. NN |-> { x e. S | ( F ` n ) = ( x i^i D ) } )
  assume subsaliuncllem.e: |- E = ( H o. G )
  assume subsaliuncllem.h: |- ( ph -> H Fn ran G )
  assume subsaliuncllem.y: |- ( ph -> A. y e. ran G ( H ` y ) e. y )

  disjoint D e
  disjoint D x
  disjoint E e
  disjoint E n
  disjoint e n
  disjoint E x
  disjoint n x
  disjoint F e
  disjoint F x
  disjoint G y
  disjoint H y
  disjoint S e
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint n y
  disjoint n ph
  disjoint k x
  assert |- ( ph -> E. e e. ( S ^m NN ) A. n e. NN ( F ` n ) = ( ( e ` n ) i^i D ) )

  proof
    wph
    cE
    cS
    cn
    cmap
    co
    #
    wcel
    vn
    cv
    #
    cF
    cfv
    #
    @1
    cE
    cfv
    #
    cD
    cin
    #
    wceq
    #
    vn
    cn
    wral
    #
    @2
    @1
    ve
    cv
    #
    cfv
    #
    cD
    cin
    #
    wceq
    #
    vn
    cn
    wral
    #
    ve
    @0
    wrex
    wph
    cE
    cH
    cG
    ccom
    #
    @0
    subsaliuncllem.e
    wph
    @12
    @0
    wcel
    cn
    cS
    @12
    wf
    #
    wph
    cG
    crn
    #
    cS
    cH
    wf
    #
    cn
    @14
    cG
    wf
    #
    @13
    wph
    cH
    @14
    wfn
    #
    vy
    cv
    #
    cH
    cfv
    #
    cS
    wcel
    #
    vy
    @14
    wral
    #
    wa
    @15
    wph
    @17
    @21
    subsaliuncllem.h
    wph
    @20
    vy
    @14
    subsaliuncllem.f
    wph
    @18
    @14
    wcel
    #
    @20
    wph
    @22
    wa
    @18
    cS
    @19
    @22
    @18
    cS
    wss
    #
    wph
    @22
    @18
    @2
    vx
    cv
    #
    cD
    cin
    #
    wceq
    #
    vx
    cS
    crab
    #
    wceq
    #
    vn
    cn
    wrex
    #
    @23
    @22
    @29
    @18
    cvv
    wcel
    @22
    @29
    wb
    vy
    vex
    vn
    cn
    @27
    @18
    cG
    cvv
    subsaliuncllem.g
    elrnmpt
    ax-mp
    biimpi
    @29
    @23
    wi
    @22
    @28
    @23
    vn
    cn
    @28
    @23
    wi
    @1
    cn
    wcel
    #
    @28
    @18
    @27
    cS
    @28
    id
    @27
    cS
    wss
    @28
    @26
    vx
    cS
    ssrab2
    a1i
    eqsstrd
    a1i
    rexlimiv
    a1i
    mpd
    adantl
    wph
    @19
    @18
    wcel
    #
    vy
    @14
    subsaliuncllem.y
    r19.21bi
    sseldd
    ex
    ralrimi
    jca
    vy
    @14
    cS
    cH
    ffnfv
    sylibr
    wph
    cG
    cn
    wfn
    #
    @16
    wph
    @27
    cvv
    wcel
    #
    vn
    cn
    wral
    #
    @32
    wph
    @33
    vn
    cn
    wph
    @26
    vx
    cS
    @27
    cV
    @27
    eqid
    subsaliuncllem.s
    rabexd
    #
    ralrimivw
    #
    vn
    cn
    @27
    cG
    cvv
    subsaliuncllem.g
    fnmpt
    syl
    cn
    cG
    dffn3
    sylib
    #
    cn
    @14
    cS
    cH
    cG
    fco
    syl2anc
    wph
    cS
    cn
    @12
    cV
    cvv
    subsaliuncllem.s
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    elmapd
    mpbird
    syl5eqel
    wph
    @5
    vn
    cn
    wph
    @30
    wa
    #
    @3
    cS
    wcel
    #
    @5
    @38
    @3
    @27
    wcel
    #
    @39
    @5
    wa
    @38
    @40
    @1
    cG
    cfv
    #
    cH
    cfv
    #
    @41
    wcel
    #
    @38
    @41
    @14
    wcel
    @31
    vy
    @14
    wral
    #
    @43
    wph
    cn
    @14
    @1
    cG
    @37
    ffvelrnda
    wph
    @44
    @30
    subsaliuncllem.y
    adantr
    @31
    @43
    vy
    @41
    @14
    @18
    @41
    wceq
    #
    @19
    @42
    @18
    @41
    @18
    @41
    cH
    fveq2
    @45
    id
    eleq12d
    rspcva
    syl2anc
    @38
    @3
    @42
    @27
    @41
    @38
    @1
    cH
    cG
    cE
    wph
    cG
    wfun
    @30
    wph
    cn
    @14
    cG
    @37
    ffund
    adantr
    @38
    @1
    cn
    cG
    cdm
    #
    wph
    @30
    simpr
    wph
    cn
    @46
    wceq
    @30
    wph
    @46
    cn
    wph
    @46
    vn
    cn
    @27
    cmpt
    #
    cdm
    #
    cn
    @46
    @48
    wceq
    wph
    cG
    @47
    subsaliuncllem.g
    dmeqi
    a1i
    wph
    @34
    @48
    cn
    wceq
    @36
    vn
    cn
    @27
    cvv
    dmmptg
    syl
    eqtrd
    eqcomd
    adantr
    eleqtrd
    subsaliuncllem.e
    fvcod
    @38
    @41
    @27
    wph
    vn
    cn
    @27
    cG
    cvv
    cG
    @47
    wceq
    wph
    subsaliuncllem.g
    a1i
    wph
    @33
    @30
    @35
    adantr
    fvmpt2d
    eqcomd
    eleq12d
    mpbird
    @26
    @5
    vx
    @3
    cS
    @24
    @3
    wceq
    @25
    @4
    @2
    @24
    @3
    cD
    ineq1
    eqeq2d
    elrab
    sylib
    simprd
    ralrimiva
    @11
    @6
    ve
    cE
    @0
    @7
    cE
    wceq
    #
    @10
    @5
    vn
    cn
    @49
    @9
    @4
    @2
    @49
    @8
    @3
    cD
    @1
    @7
    cE
    fveq1
    ineq1d
    eqeq2d
    ralbidv
    rspcev
    syl2anc
end
