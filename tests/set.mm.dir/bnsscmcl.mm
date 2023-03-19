include "ccbn.mm"
include "wcel.mm"
include "wa.mm"
include "cims.mm"
include "cfv.mm"
include "cms.mm"
include "cxp.mm"
include "cres.mm"
include "ccld.mm"
include "cnv.mm"
include "wb.mm"
include "bnnv.mm"
include "sspnv.mm"
include "sylan.mm"
include "eqid.mm"
include "iscbn.mm"
include "baib.mm"
include "syl.mm"
include "wceq.mm"
include "sspims.mm"
include "eleq1d.mm"
include "cbncms.mm"
include "adantr.mm"
include "cmetss.mm"
include "3bitrd.mm"

theorem bnsscmcl
  let cD: class D
  let cU: class U
  let cH: class H
  let cJ: class J
  let cW: class W
  let cX: class X
  let cY: class Y
  assume bnsscmcl.x: |- X = ( BaseSet ` U )
  assume bnsscmcl.d: |- D = ( IndMet ` U )
  assume bnsscmcl.j: |- J = ( MetOpen ` D )
  assume bnsscmcl.h: |- H = ( SubSp ` U )
  assume bnsscmcl.y: |- Y = ( BaseSet ` W )


  assert |- ( ( U e. CBan /\ W e. H ) -> ( W e. CBan <-> Y e. ( Clsd ` J ) ) )

  proof
    cU
    ccbn
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cW
    ccbn
    wcel
    #
    cW
    cims
    cfv
    #
    cY
    cms
    cfv
    #
    wcel
    #
    cD
    cY
    cY
    cxp
    cres
    #
    @5
    wcel
    #
    cY
    cJ
    ccld
    cfv
    wcel
    #
    @2
    cW
    cnv
    wcel
    #
    @3
    @6
    wb
    @0
    cU
    cnv
    wcel
    #
    @1
    @10
    cU
    bnnv
    #
    cU
    cH
    cW
    bnsscmcl.h
    sspnv
    sylan
    @3
    @10
    @6
    @4
    cW
    cY
    bnsscmcl.y
    @4
    eqid
    #
    iscbn
    baib
    syl
    @2
    @4
    @7
    @5
    @0
    @11
    @1
    @4
    @7
    wceq
    @12
    @4
    cD
    cU
    cH
    cW
    cY
    bnsscmcl.y
    bnsscmcl.d
    @13
    bnsscmcl.h
    sspims
    sylan
    eleq1d
    @2
    cD
    cX
    cms
    cfv
    wcel
    #
    @8
    @9
    wb
    @0
    @14
    @1
    cD
    cU
    cX
    bnsscmcl.x
    bnsscmcl.d
    cbncms
    adantr
    cD
    cJ
    cX
    cY
    bnsscmcl.j
    cmetss
    syl
    3bitrd
end
