include "cims.mm"
include "cfv.mm"
include "cno.mm"
include "cmv.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "eqid.mm"
include "hhssims.mm"
include "eqtr4i.mm"

theorem hhssims2
  let cD: class D
  let cH: class H
  let cW: class W
  assume hhssims2.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.
  assume hhssims2.3: |- D = ( IndMet ` W )
  assume hhssims2.2: |- H e. SH


  assert |- D = ( ( normh o. -h ) |` ( H X. H ) )

  proof
    cD
    cW
    cims
    cfv
    cno
    cmv
    ccom
    cH
    cH
    cxp
    cres
    #
    hhssims2.3
    @0
    cH
    cW
    hhssims2.1
    hhssims2.2
    @0
    eqid
    hhssims
    eqtr4i
end
