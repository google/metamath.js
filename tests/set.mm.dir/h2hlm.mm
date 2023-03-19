include "chli.mm"
include "clm.mm"
include "cfv.mm"
include "chil.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cres.mm"
include "cv.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cmv.mm"
include "cno.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "df-hlim.mm"
include "relopabi.mm"
include "relres.mm"
include "cop.mm"
include "copab.mm"
include "eleq2i.mm"
include "opabid.mm"
include "ancom.mm"
include "hlex.mm"
include "nnex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "df-br.mm"
include "c1.mm"
include "cnv.mm"
include "cxmt.mm"
include "imsxmet.mm"
include "mp1i.mm"
include "nnuz.mm"
include "1zzd.mm"
include "eqidd.mm"
include "id.mm"
include "lmmbrf.mm"
include "wb.mm"
include "eluznn.mm"
include "wceq.mm"
include "ffvelrn.mm"
include "h2hmetdval.mm"
include "sylan.mm"
include "breq1d.mm"
include "an32s.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "syl5bbr.mm"
include "pm5.32i.mm"
include "3bitrri.mm"
include "anass.mm"
include "vex.mm"
include "opelres.mm"
include "3bitr4i.mm"
include "3bitri.mm"
include "eqrelriiv.mm"

theorem h2hlm
  let cD: class D
  let cU: class U
  let cJ: class J
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vj: setvar j
  let vk: setvar k
  assume h2hl.1: |- U = <. <. +h , .h >. , normh >.
  assume h2hl.2: |- U e. NrmCVec
  assume h2hl.3: |- ~H = ( BaseSet ` U )
  assume h2hl.4: |- D = ( IndMet ` U )
  assume h2hl.5: |- J = ( MetOpen ` D )


  assert |- ~~>v = ( ( ~~>t ` J ) |` ( ~H ^m NN ) )

  proof
    vf
    vx
    chli
    cJ
    clm
    cfv
    #
    chil
    cn
    cmap
    co
    #
    cres
    #
    cn
    chil
    vf
    cv
    #
    wf
    #
    vx
    cv
    #
    chil
    wcel
    #
    wa
    #
    vk
    cv
    #
    @3
    cfv
    #
    @5
    cmv
    co
    cno
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cn
    wrex
    #
    vy
    crp
    wral
    #
    wa
    #
    vf
    vx
    chli
    vy
    vj
    vk
    vx
    vf
    df-hlim
    #
    relopabi
    @0
    @1
    relres
    @3
    @5
    cop
    #
    chli
    wcel
    @20
    @18
    vf
    vx
    copab
    #
    wcel
    @18
    @20
    @2
    wcel
    #
    chli
    @21
    @20
    @19
    eleq2i
    @18
    vf
    vx
    opabid
    @4
    @6
    @17
    wa
    #
    wa
    #
    @20
    @0
    wcel
    #
    @3
    @1
    wcel
    #
    wa
    #
    @18
    @22
    @27
    @26
    @25
    wa
    @4
    @25
    wa
    @24
    @25
    @26
    ancom
    @26
    @4
    @25
    chil
    cn
    @3
    cU
    chil
    h2hl.3
    hlex
    nnex
    elmap
    anbi1i
    @4
    @25
    @23
    @25
    @3
    @5
    @0
    wbr
    #
    @4
    @23
    @3
    @5
    @0
    df-br
    @4
    @28
    @6
    @9
    @5
    cD
    co
    #
    @11
    clt
    wbr
    #
    vk
    @14
    wral
    #
    vj
    cn
    wrex
    #
    vy
    crp
    wral
    #
    wa
    @23
    @4
    vy
    @9
    cD
    @5
    vj
    vk
    @3
    cJ
    c1
    chil
    cn
    h2hl.5
    cU
    cnv
    wcel
    cD
    chil
    cxmt
    cfv
    wcel
    @4
    h2hl.2
    cD
    cU
    chil
    h2hl.3
    h2hl.4
    imsxmet
    mp1i
    nnuz
    @4
    1zzd
    @4
    @8
    cn
    wcel
    #
    wa
    #
    @9
    eqidd
    @4
    id
    lmmbrf
    @4
    @6
    @33
    @17
    @7
    @32
    @16
    vy
    crp
    @7
    @31
    @15
    vj
    cn
    @7
    @13
    cn
    wcel
    #
    wa
    @30
    @12
    vk
    @14
    @7
    @36
    @8
    @14
    wcel
    #
    @30
    @12
    wb
    #
    @36
    @37
    wa
    @7
    @34
    @38
    @8
    @13
    eluznn
    @4
    @34
    @6
    @38
    @35
    @6
    wa
    @29
    @10
    @11
    clt
    @35
    @9
    chil
    wcel
    @6
    @29
    @10
    wceq
    cn
    chil
    @8
    @3
    ffvelrn
    @9
    @5
    cD
    cU
    h2hl.1
    h2hl.2
    h2hl.3
    h2hl.4
    h2hmetdval
    sylan
    breq1d
    an32s
    sylan2
    anassrs
    ralbidva
    rexbidva
    ralbidv
    pm5.32da
    bitrd
    syl5bbr
    pm5.32i
    3bitrri
    @4
    @6
    @17
    anass
    @3
    @5
    @0
    @1
    vx
    vex
    opelres
    3bitr4i
    3bitri
    eqrelriiv
end
