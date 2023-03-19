include "wcel.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "c0.mm"
include "wne.mm"
include "c2o.mm"
include "2on0.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "cvv.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "eqid.mm"
include "pmtrfrn.mm"
include "simpld.mm"
include "simp3d.mm"
include "enen1.mm"
include "syl.mm"
include "en0.mm"
include "3bitr3g.mm"
include "necon3bid.mm"
include "mpbiri.mm"

theorem pmtrfmvdn0
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


  assert |- ( F e. R -> dom ( F \ _I ) =/= (/) )

  proof
    cF
    cR
    wcel
    #
    cF
    cid
    cdif
    cdm
    #
    c0
    wne
    c2o
    c0
    wne
    2on0
    @0
    @1
    c0
    c2o
    c0
    @0
    @1
    c0
    cen
    wbr
    #
    c2o
    c0
    cen
    wbr
    #
    @1
    c0
    wceq
    c2o
    c0
    wceq
    @0
    @1
    c2o
    cen
    wbr
    #
    @2
    @3
    wb
    @0
    cD
    cvv
    wcel
    #
    @1
    cD
    wss
    #
    @4
    @0
    @5
    @6
    @4
    w3a
    cF
    @1
    cT
    cfv
    wceq
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
    simpld
    simp3d
    @1
    c2o
    c0
    enen1
    syl
    @1
    en0
    c2o
    en0
    3bitr3g
    necon3bid
    mpbiri
end
