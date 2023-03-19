include "cc.mm"
include "wcel.mm"
include "cxr.mm"
include "wa.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "cxmt.mm"
include "wss.mm"
include "cnxmet.mm"
include "blssm.mm"
include "mp3an1.mm"
include "syl5eqss.mm"
include "cv.mm"
include "blcvx.mm"
include "cvxsconn.mm"

theorem blsconn
  let cP: class P
  let cR: class R
  let cS: class S
  let cJ: class J
  let cK: class K
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  assume blsconn.j: |- J = ( TopOpen ` CCfld )
  assume blsconn.s: |- S = ( P ( ball ` ( abs o. - ) ) R )
  assume blsconn.k: |- K = ( J |`t S )


  assert |- ( ( P e. CC /\ R e. RR* ) -> K e. SConn )

  proof
    cP
    cc
    wcel
    #
    cR
    cxr
    wcel
    #
    wa
    #
    vx
    vy
    vt
    cS
    cJ
    cK
    @2
    cS
    cP
    cR
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    cc
    blsconn.s
    @3
    cc
    cxmt
    cfv
    wcel
    @0
    @1
    @4
    cc
    wss
    cnxmet
    @3
    cP
    cR
    cc
    blssm
    mp3an1
    syl5eqss
    vx
    cv
    vy
    cv
    cP
    cR
    cS
    vt
    cv
    blsconn.s
    blcvx
    blsconn.j
    blsconn.k
    cvxsconn
end
