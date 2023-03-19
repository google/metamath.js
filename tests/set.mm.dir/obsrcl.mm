include "cobs.mm"
include "cfv.mm"
include "wcel.mm"
include "cphl.mm"
include "cbs.mm"
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
include "simp1bi.mm"

theorem obsrcl
  let cB: class B
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( B e. ( OBasis ` W ) -> W e. PreHil )

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
    cW
    cbs
    cfv
    #
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
    @1
    @2
    wceq
    cW
    csca
    cfv
    #
    cur
    cfv
    #
    @4
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
    @5
    @4
    @3
    @7
    @0
    cW
    @8
    @6
    @0
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
    @8
    eqid
    isobs
    simp1bi
end
