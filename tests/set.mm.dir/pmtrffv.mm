include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "cif.mm"
include "wceq.mm"
include "cvv.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "pmtrfrn.mm"
include "simprd.mm"
include "fveq1d.mm"
include "adantr.mm"
include "simpld.mm"
include "pmtrfv.mm"
include "sylan.mm"
include "eqtrd.mm"

theorem pmtrffv
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cZ: class Z
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  assume pmtrrn.t: |- T = ( pmTrsp ` D )
  assume pmtrrn.r: |- R = ran T
  assume pmtrfrn.p: |- P = dom ( F \ _I )


  assert |- ( ( F e. R /\ Z e. D ) -> ( F ` Z ) = if ( Z e. P , U. ( P \ { Z } ) , Z ) )

  proof
    cF
    cR
    wcel
    #
    cZ
    cD
    wcel
    #
    wa
    cZ
    cF
    cfv
    #
    cZ
    cP
    cT
    cfv
    #
    cfv
    #
    cZ
    cP
    wcel
    cP
    cZ
    csn
    cdif
    cuni
    cZ
    cif
    #
    @0
    @2
    @4
    wceq
    @1
    @0
    cZ
    cF
    @3
    @0
    cD
    cvv
    wcel
    cP
    cD
    wss
    cP
    c2o
    cen
    wbr
    w3a
    #
    cF
    @3
    wceq
    #
    cD
    cP
    cR
    cT
    cF
    pmtrrn.t
    pmtrrn.r
    pmtrfrn.p
    pmtrfrn
    #
    simprd
    fveq1d
    adantr
    @0
    @6
    @1
    @4
    @5
    wceq
    @0
    @6
    @7
    @8
    simpld
    cD
    cP
    cT
    cvv
    cZ
    pmtrrn.t
    pmtrfv
    sylan
    eqtrd
end
