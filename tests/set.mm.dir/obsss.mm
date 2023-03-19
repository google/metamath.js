include "cobs.mm"
include "cfv.mm"
include "wcel.mm"
include "cphl.mm"
include "wss.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "wceq.mm"
include "csca.mm"
include "cur.mm"
include "c0g.mm"
include "cif.mm"
include "wral.mm"
include "cocv.mm"
include "csn.mm"
include "wa.mm"
include "eqid.mm"
include "isobs.mm"
include "simp2bi.mm"

theorem obsss
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume obsss.v: |- V = ( Base ` W )


  assert |- ( B e. ( OBasis ` W ) -> B C_ V )

  proof
    cB
    cW
    cobs
    cfv
    wcel
    cW
    cphl
    wcel
    cB
    cV
    wss
    vx
    cv
    #
    vy
    cv
    #
    cW
    cip
    cfv
    #
    co
    @0
    @1
    wceq
    cW
    csca
    cfv
    #
    cur
    cfv
    #
    @3
    c0g
    cfv
    #
    cif
    wceq
    vy
    cB
    wral
    vx
    cB
    wral
    cB
    cW
    cocv
    cfv
    #
    cfv
    cW
    c0g
    cfv
    #
    csn
    wceq
    wa
    vx
    vy
    cB
    @4
    @3
    @2
    @6
    cV
    cW
    @7
    @5
    obsss.v
    @2
    eqid
    @3
    eqid
    @4
    eqid
    @5
    eqid
    @6
    eqid
    @7
    eqid
    isobs
    simp2bi
end
