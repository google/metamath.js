include "cnv.mm"
include "wcel.mm"
include "cpv.mm"
include "cfv.mm"
include "wss.mm"
include "cns.mm"
include "cnmcv.mm"
include "w3a.mm"
include "eqid.mm"
include "isssp.mm"
include "simprbda.mm"

theorem sspnv
  let cU: class U
  let cH: class H
  let cW: class W
  assume sspnv.h: |- H = ( SubSp ` U )


  assert |- ( ( U e. NrmCVec /\ W e. H ) -> W e. NrmCVec )

  proof
    cU
    cnv
    wcel
    cW
    cH
    wcel
    cW
    cnv
    wcel
    cW
    cpv
    cfv
    #
    cU
    cpv
    cfv
    #
    wss
    cW
    cns
    cfv
    #
    cU
    cns
    cfv
    #
    wss
    cW
    cnmcv
    cfv
    #
    cU
    cnmcv
    cfv
    #
    wss
    w3a
    @2
    @3
    cU
    @0
    @1
    cH
    @4
    @5
    cW
    @1
    eqid
    @0
    eqid
    @3
    eqid
    @2
    eqid
    @5
    eqid
    @4
    eqid
    sspnv.h
    isssp
    simprbda
end
