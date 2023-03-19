include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cpv.mm"
include "cfv.mm"
include "crn.mm"
include "wss.mm"
include "cns.mm"
include "cnmcv.mm"
include "w3a.mm"
include "eqid.mm"
include "isssp.mm"
include "simplbda.mm"
include "simp1d.mm"
include "rnss.mm"
include "syl.mm"
include "bafval.mm"
include "3sstr4g.mm"

theorem sspba
  let cU: class U
  let cH: class H
  let cW: class W
  let cX: class X
  let cY: class Y
  assume sspba.x: |- X = ( BaseSet ` U )
  assume sspba.y: |- Y = ( BaseSet ` W )
  assume sspba.h: |- H = ( SubSp ` U )


  assert |- ( ( U e. NrmCVec /\ W e. H ) -> Y C_ X )

  proof
    cU
    cnv
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cW
    cpv
    cfv
    #
    crn
    #
    cU
    cpv
    cfv
    #
    crn
    #
    cY
    cX
    @2
    @3
    @5
    wss
    #
    @4
    @6
    wss
    @2
    @7
    cW
    cns
    cfv
    #
    cU
    cns
    cfv
    #
    wss
    #
    cW
    cnmcv
    cfv
    #
    cU
    cnmcv
    cfv
    #
    wss
    #
    @0
    @1
    cW
    cnv
    wcel
    @7
    @10
    @13
    w3a
    @8
    @9
    cU
    @3
    @5
    cH
    @11
    @12
    cW
    @5
    eqid
    #
    @3
    eqid
    #
    @9
    eqid
    @8
    eqid
    @12
    eqid
    @11
    eqid
    sspba.h
    isssp
    simplbda
    simp1d
    @3
    @5
    rnss
    syl
    cW
    @3
    cY
    sspba.y
    @15
    bafval
    cU
    @5
    cX
    sspba.x
    @14
    bafval
    3sstr4g
end
