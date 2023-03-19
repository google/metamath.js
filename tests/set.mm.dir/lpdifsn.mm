include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "clp.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "ccl.mm"
include "islp.mm"
include "wb.mm"
include "ssdifss.mm"
include "sylan2.mm"
include "difabs.mm"
include "fveq2i.mm"
include "eleq2i.mm"
include "syl6bb.mm"
include "bitr4d.mm"

theorem lpdifsn
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


  assert |- ( ( J e. Top /\ S C_ X ) -> ( P e. ( ( limPt ` J ) ` S ) <-> P e. ( ( limPt ` J ) ` ( S \ { P } ) ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cP
    cS
    cJ
    clp
    cfv
    #
    cfv
    wcel
    cP
    cS
    cP
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
    cP
    @5
    @3
    cfv
    wcel
    #
    cP
    cS
    cJ
    cX
    lpfval.1
    islp
    @2
    @9
    cP
    @5
    @4
    cdif
    #
    @6
    cfv
    #
    wcel
    #
    @8
    @1
    @0
    @5
    cX
    wss
    @9
    @12
    wb
    cS
    cX
    @4
    ssdifss
    cP
    @5
    cJ
    cX
    lpfval.1
    islp
    sylan2
    @11
    @7
    cP
    @10
    @5
    @6
    cS
    @4
    difabs
    fveq2i
    eleq2i
    syl6bb
    bitr4d
end
