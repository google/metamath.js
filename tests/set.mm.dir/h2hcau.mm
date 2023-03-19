include "cv.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "crp.mm"
include "chil.mm"
include "cmap.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "ccau.mm"
include "cca.mm"
include "cin.mm"
include "df-rab.mm"
include "df-hcau.mm"
include "elin.mm"
include "ancom.mm"
include "wf.mm"
include "wb.mm"
include "hlex.mm"
include "nnex.mm"
include "elmap.mm"
include "c1.mm"
include "nnuz.mm"
include "cnv.mm"
include "cxmt.mm"
include "imsxmet.mm"
include "mp1i.mm"
include "1zzd.mm"
include "eqidd.mm"
include "id.mm"
include "iscauf.mm"
include "wceq.mm"
include "ffvelrn.mm"
include "adantr.mm"
include "eluznn.mm"
include "sylan2.mm"
include "anassrs.mm"
include "h2hmetdval.mm"
include "syl2anc.mm"
include "breq1d.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "bitrd.mm"
include "sylbi.mm"
include "pm5.32i.mm"
include "3bitri.mm"
include "abbi2i.mm"
include "3eqtr4i.mm"

theorem h2hcau
  let cD: class D
  let cU: class U
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume h2hc.1: |- U = <. <. +h , .h >. , normh >.
  assume h2hc.2: |- U e. NrmCVec
  assume h2hc.3: |- ~H = ( BaseSet ` U )
  assume h2hc.4: |- D = ( IndMet ` U )


  assert |- Cauchy = ( ( Cau ` D ) i^i ( ~H ^m NN ) )

  proof
    vj
    cv
    #
    vf
    cv
    #
    cfv
    #
    vk
    cv
    #
    @1
    cfv
    #
    cmv
    co
    cno
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vk
    @0
    cuz
    cfv
    #
    wral
    #
    vj
    cn
    wrex
    #
    vx
    crp
    wral
    #
    vf
    chil
    cn
    cmap
    co
    #
    crab
    @1
    @12
    wcel
    #
    @11
    wa
    #
    vf
    cab
    ccau
    cD
    cca
    cfv
    #
    @12
    cin
    #
    @11
    vf
    @12
    df-rab
    vx
    vj
    vk
    vf
    df-hcau
    @14
    vf
    @16
    @1
    @16
    wcel
    @1
    @15
    wcel
    #
    @13
    wa
    @13
    @17
    wa
    @14
    @1
    @15
    @12
    elin
    @17
    @13
    ancom
    @13
    @17
    @11
    @13
    cn
    chil
    @1
    wf
    #
    @17
    @11
    wb
    chil
    cn
    @1
    cU
    chil
    h2hc.3
    hlex
    nnex
    elmap
    @18
    @17
    @2
    @4
    cD
    co
    #
    @6
    clt
    wbr
    #
    vk
    @8
    wral
    #
    vj
    cn
    wrex
    #
    vx
    crp
    wral
    @11
    @18
    vx
    @4
    @2
    cD
    vj
    vk
    @1
    c1
    chil
    cn
    nnuz
    cU
    cnv
    wcel
    cD
    chil
    cxmt
    cfv
    wcel
    @18
    h2hc.2
    cD
    cU
    chil
    h2hc.3
    h2hc.4
    imsxmet
    mp1i
    @18
    1zzd
    @18
    @3
    cn
    wcel
    #
    wa
    @4
    eqidd
    @18
    @0
    cn
    wcel
    #
    wa
    #
    @2
    eqidd
    @18
    id
    iscauf
    @18
    @22
    @10
    vx
    crp
    @18
    @21
    @9
    vj
    cn
    @25
    @20
    @7
    vk
    @8
    @25
    @3
    @8
    wcel
    #
    wa
    #
    @19
    @5
    @6
    clt
    @27
    @2
    chil
    wcel
    #
    @4
    chil
    wcel
    #
    @19
    @5
    wceq
    @25
    @28
    @26
    cn
    chil
    @0
    @1
    ffvelrn
    adantr
    @18
    @24
    @26
    @29
    @24
    @26
    wa
    @18
    @23
    @29
    @3
    @0
    eluznn
    cn
    chil
    @3
    @1
    ffvelrn
    sylan2
    anassrs
    @2
    @4
    cD
    cU
    h2hc.1
    h2hc.2
    h2hc.3
    h2hc.4
    h2hmetdval
    syl2anc
    breq1d
    ralbidva
    rexbidva
    ralbidv
    bitrd
    sylbi
    pm5.32i
    3bitri
    abbi2i
    3eqtr4i
end
