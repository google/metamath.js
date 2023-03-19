include "cmopn.mm"
include "cfv.mm"
include "chil.mm"
include "eqid.mm"
include "hhmet.mm"
include "cv.mm"
include "cca.mm"
include "wcel.mm"
include "cn.mm"
include "wf.mm"
include "wa.mm"
include "chli.mm"
include "wbr.mm"
include "wrex.mm"
include "clm.mm"
include "cdm.mm"
include "ccau.mm"
include "cmap.mm"
include "co.mm"
include "cin.mm"
include "hhcau.mm"
include "eleq2i.mm"
include "elin.mm"
include "ax-hilex.mm"
include "nnex.mm"
include "elmap.mm"
include "anbi2i.mm"
include "bitri.mm"
include "ax-hcompl.mm"
include "sylbir.mm"
include "cres.mm"
include "hhlm.mm"
include "breqi.mm"
include "vex.mm"
include "brres.mm"
include "breldm.mm"
include "adantr.mm"
include "sylbi.mm"
include "rexlimivw.mm"
include "syl.mm"
include "iscmet3i.mm"

theorem hhcms
  let cD: class D
  let cU: class U
  let vf: setvar f
  let vx: setvar x
  assume hhcms.1: |- U = <. <. +h , .h >. , normh >.
  assume hhcms.2: |- D = ( IndMet ` U )


  assert |- D e. ( CMet ` ~H )

  proof
    cD
    vf
    cD
    cmopn
    cfv
    #
    chil
    @0
    eqid
    #
    cD
    cU
    hhcms.1
    hhcms.2
    hhmet
    vf
    cv
    #
    cD
    cca
    cfv
    #
    wcel
    #
    cn
    chil
    @2
    wf
    #
    wa
    #
    @2
    vx
    cv
    #
    chli
    wbr
    #
    vx
    chil
    wrex
    #
    @2
    @0
    clm
    cfv
    #
    cdm
    wcel
    #
    @6
    @2
    ccau
    wcel
    #
    @9
    @12
    @2
    @3
    chil
    cn
    cmap
    co
    #
    cin
    #
    wcel
    #
    @6
    ccau
    @14
    @2
    cD
    cU
    hhcms.1
    hhcms.2
    hhcau
    eleq2i
    @15
    @4
    @2
    @13
    wcel
    #
    wa
    @6
    @2
    @3
    @13
    elin
    @16
    @5
    @4
    chil
    cn
    @2
    ax-hilex
    nnex
    elmap
    anbi2i
    bitri
    bitri
    vx
    @2
    ax-hcompl
    sylbir
    @8
    @11
    vx
    chil
    @8
    @2
    @7
    @10
    wbr
    #
    @16
    wa
    #
    @11
    @8
    @2
    @7
    @10
    @13
    cres
    #
    wbr
    @18
    @2
    @7
    chli
    @19
    cD
    cU
    @0
    hhcms.1
    hhcms.2
    @1
    hhlm
    breqi
    @2
    @7
    @10
    @13
    vx
    vex
    #
    brres
    bitri
    @17
    @11
    @16
    @2
    @7
    @10
    vf
    vex
    @20
    breldm
    adantr
    sylbi
    rexlimivw
    syl
    iscmet3i
end
