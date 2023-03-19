include "cno.mm"
include "cmv.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cims.mm"
include "cfv.mm"
include "cnv.mm"
include "wcel.mm"
include "wceq.mm"
include "hhssnv.mm"
include "hhssvs.mm"
include "hhssnm.mm"
include "eqid.mm"
include "imsval.mm"
include "ax-mp.mm"
include "resco.mm"
include "crn.mm"
include "wss.mm"
include "wf.mm"
include "hhssvsf.mm"
include "frn.mm"
include "cores.mm"
include "eqtr4i.mm"

theorem hhssims
  let cD: class D
  let cH: class H
  let cW: class W
  assume hhsssh2.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.
  assume hhssims.2: |- H e. SH
  assume hhssims.3: |- D = ( ( normh o. -h ) |` ( H X. H ) )


  assert |- D = ( IndMet ` W )

  proof
    cD
    cno
    cmv
    ccom
    cH
    cH
    cxp
    #
    cres
    #
    cW
    cims
    cfv
    #
    hhssims.3
    @2
    cno
    cH
    cres
    #
    cmv
    @0
    cres
    #
    ccom
    #
    @1
    cW
    cnv
    wcel
    @2
    @5
    wceq
    cH
    cW
    hhsssh2.1
    hhssims.2
    hhssnv
    @2
    cW
    @4
    @3
    cH
    cW
    hhsssh2.1
    hhssims.2
    hhssvs
    cH
    cW
    hhsssh2.1
    hhssnm
    @2
    eqid
    imsval
    ax-mp
    @1
    cno
    @4
    ccom
    #
    @5
    cno
    cmv
    @0
    resco
    @4
    crn
    cH
    wss
    #
    @5
    @6
    wceq
    @0
    cH
    @4
    wf
    @7
    cH
    cW
    hhsssh2.1
    hhssims.2
    hhssvsf
    @0
    cH
    @4
    frn
    ax-mp
    cno
    @4
    cH
    cores
    ax-mp
    eqtr4i
    eqtr4i
    eqtr4i
end
