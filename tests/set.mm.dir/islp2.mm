include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "clp.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "ccl.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cnei.mm"
include "wral.mm"
include "wb.mm"
include "islp.mm"
include "3adant3.mm"
include "ssdifss.mm"
include "neindisj2.mm"
include "syl3an2.mm"
include "bitrd.mm"

theorem islp2
  let cP: class P
  let cS: class S
  let vn: setvar n
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  assume lpfval.1: |- X = U. J

  disjoint J n
  disjoint P n
  disjoint S n
  disjoint X n
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint P x
  disjoint P y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint X j
  disjoint X x
  disjoint X y
  assert |- ( ( J e. Top /\ S C_ X /\ P e. X ) -> ( P e. ( ( limPt ` J ) ` S ) <-> A. n e. ( ( nei ` J ) ` { P } ) ( n i^i ( S \ { P } ) ) =/= (/) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cP
    cX
    wcel
    #
    w3a
    cP
    cS
    cJ
    clp
    cfv
    cfv
    wcel
    #
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
    cfv
    wcel
    #
    vn
    cv
    @5
    cin
    c0
    wne
    vn
    @4
    cJ
    cnei
    cfv
    cfv
    wral
    #
    @0
    @1
    @3
    @6
    wb
    @2
    cP
    cS
    cJ
    cX
    lpfval.1
    islp
    3adant3
    @1
    @0
    @5
    cX
    wss
    @2
    @6
    @7
    wb
    cS
    cX
    @4
    ssdifss
    cP
    @5
    vn
    cJ
    cX
    lpfval.1
    neindisj2
    syl3an2
    bitrd
end
