include "cnp.mm"
include "cnq.mm"
include "cpw.mm"
include "nqex.mm"
include "pwex.mm"
include "c0.mm"
include "cv.mm"
include "wpss.mm"
include "wa.mm"
include "cltq.mm"
include "wbr.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wral.mm"
include "cab.mm"
include "wss.mm"
include "pssss.mm"
include "ad2antlr.mm"
include "ss2abi.mm"
include "df-np.mm"
include "df-pw.mm"
include "3sstr4i.mm"
include "ssexi.mm"

theorem npex
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- P. e. _V

  proof
    cnp
    cnq
    cpw
    #
    cnq
    nqex
    pwex
    c0
    vx
    cv
    #
    wpss
    #
    @1
    cnq
    wpss
    #
    wa
    vz
    cv
    #
    vy
    cv
    #
    cltq
    wbr
    vz
    vx
    wel
    wi
    vz
    wal
    @5
    @4
    cltq
    wbr
    vz
    @1
    wrex
    wa
    vy
    @1
    wral
    #
    wa
    #
    vx
    cab
    @1
    cnq
    wss
    #
    vx
    cab
    cnp
    @0
    @7
    @8
    vx
    @3
    @8
    @2
    @6
    @1
    cnq
    pssss
    ad2antlr
    ss2abi
    vx
    vy
    vz
    df-np
    vx
    cnq
    df-pw
    3sstr4i
    ssexi
end
