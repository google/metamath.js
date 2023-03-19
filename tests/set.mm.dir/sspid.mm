include "cnv.mm"
include "wcel.mm"
include "cpv.mm"
include "cfv.mm"
include "wss.mm"
include "cns.mm"
include "cnmcv.mm"
include "w3a.mm"
include "wa.mm"
include "ssid.mm"
include "3pm3.2i.mm"
include "jctr.mm"
include "eqid.mm"
include "isssp.mm"
include "mpbird.mm"

theorem sspid
  let cU: class U
  let cH: class H
  assume sspid.h: |- H = ( SubSp ` U )


  assert |- ( U e. NrmCVec -> U e. H )

  proof
    cU
    cnv
    wcel
    #
    cU
    cH
    wcel
    @0
    cU
    cpv
    cfv
    #
    @1
    wss
    #
    cU
    cns
    cfv
    #
    @3
    wss
    #
    cU
    cnmcv
    cfv
    #
    @5
    wss
    #
    w3a
    #
    wa
    @0
    @7
    @2
    @4
    @6
    @1
    ssid
    @3
    ssid
    @5
    ssid
    3pm3.2i
    jctr
    @3
    @3
    cU
    @1
    @1
    cH
    @5
    @5
    cU
    @1
    eqid
    #
    @8
    @3
    eqid
    #
    @9
    @5
    eqid
    #
    @10
    sspid.h
    isssp
    mpbird
end
