include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "clp.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "ccl.mm"
include "cab.mm"
include "lpval.mm"
include "eleq2d.mm"
include "elex.mm"
include "wceq.mm"
include "id.mm"
include "sneq.mm"
include "difeq2d.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem islp
  let cP: class P
  let cS: class S
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  assume lpfval.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X ) -> ( P e. ( ( limPt ` J ) ` S ) <-> P e. ( ( cls ` J ) ` ( S \ { P } ) ) ) )

  proof
    cJ
    ctop
    wcel
    cS
    cX
    wss
    wa
    #
    cP
    cS
    cJ
    clp
    cfv
    cfv
    #
    wcel
    cP
    vx
    cv
    #
    cS
    @2
    csn
    #
    cdif
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    wcel
    #
    vx
    cab
    #
    wcel
    cP
    cS
    cP
    csn
    #
    cdif
    #
    @5
    cfv
    #
    wcel
    #
    @0
    @1
    @8
    cP
    vx
    cS
    cJ
    cX
    lpfval.1
    lpval
    eleq2d
    @7
    @12
    vx
    cP
    cP
    @11
    elex
    @2
    cP
    wceq
    #
    @2
    cP
    @6
    @11
    @13
    id
    @13
    @4
    @10
    @5
    @13
    @3
    @9
    cS
    @2
    cP
    sneq
    difeq2d
    fveq2d
    eleq12d
    elab3
    syl6bb
end
