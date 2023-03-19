include "wcel.mm"
include "wf.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cfv.mm"
include "cvv.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "eqid.mm"
include "pmtrfrn.mm"
include "simpld.mm"
include "pmtrf.mm"
include "syl.mm"
include "simprd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "pmtrfinv.mm"
include "2fcoidinvd.mm"

theorem pmtrfcnv
  let cD: class D
  let cR: class R
  let cT: class T
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cV: class V
  assume pmtrrn.t: |- T = ( pmTrsp ` D )
  assume pmtrrn.r: |- R = ran T


  assert |- ( F e. R -> `' F = F )

  proof
    cF
    cR
    wcel
    #
    cD
    cD
    cF
    cF
    @0
    cD
    cD
    cF
    wf
    cD
    cD
    cF
    cid
    cdif
    cdm
    #
    cT
    cfv
    #
    wf
    #
    @0
    cD
    cvv
    wcel
    @1
    cD
    wss
    @1
    c2o
    cen
    wbr
    w3a
    #
    @3
    @0
    @4
    cF
    @2
    wceq
    #
    cD
    @1
    cR
    cT
    cF
    pmtrrn.t
    pmtrrn.r
    @1
    eqid
    pmtrfrn
    #
    simpld
    cD
    @1
    cT
    cvv
    pmtrrn.t
    pmtrf
    syl
    @0
    cD
    cD
    cF
    @2
    @0
    @4
    @5
    @6
    simprd
    feq1d
    mpbird
    #
    @7
    cD
    cR
    cT
    cF
    pmtrrn.t
    pmtrrn.r
    pmtrfinv
    #
    @8
    2fcoidinvd
end
