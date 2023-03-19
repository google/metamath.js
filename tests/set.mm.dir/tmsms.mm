include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxme.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cmt.mm"
include "cxmt.mm"
include "metxmet.mm"
include "tmsxms.mm"
include "syl.mm"
include "wss.mm"
include "wceq.mm"
include "tmsds.mm"
include "tmsbas.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "ibi.mm"
include "ssid.mm"
include "metres2.mm"
include "sylancl.mm"
include "ctopn.mm"
include "eqid.mm"
include "isms.mm"
include "sylanbrc.mm"

theorem tmsms
  let cD: class D
  let cK: class K
  let cX: class X
  assume tmsbas.k: |- K = ( toMetSp ` D )


  assert |- ( D e. ( Met ` X ) -> K e. MetSp )

  proof
    cD
    cX
    cme
    cfv
    #
    wcel
    #
    cK
    cxme
    wcel
    #
    cK
    cds
    cfv
    #
    cK
    cbs
    cfv
    #
    @4
    cxp
    cres
    #
    @4
    cme
    cfv
    #
    wcel
    #
    cK
    cmt
    wcel
    @1
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @2
    cD
    cX
    metxmet
    #
    cD
    cK
    cX
    tmsbas.k
    tmsxms
    syl
    @1
    @3
    @6
    wcel
    #
    @4
    @4
    wss
    @7
    @1
    @10
    @1
    cD
    @3
    @0
    @6
    @1
    @8
    cD
    @3
    wceq
    @9
    cD
    cK
    cX
    tmsbas.k
    tmsds
    syl
    @1
    cX
    @4
    cme
    @1
    @8
    cX
    @4
    wceq
    @9
    cD
    cK
    cX
    tmsbas.k
    tmsbas
    syl
    fveq2d
    eleq12d
    ibi
    @4
    ssid
    @3
    @4
    @4
    metres2
    sylancl
    @5
    cK
    ctopn
    cfv
    #
    cK
    @4
    @11
    eqid
    @4
    eqid
    @5
    eqid
    isms
    sylanbrc
end
