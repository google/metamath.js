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
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "islp.mm"
include "3adant3.mm"
include "simp2.mm"
include "ssdifssd.mm"
include "elcls.mm"
include "syld3an2.mm"
include "bitrd.mm"

theorem islp3
  let vx: setvar x
  let cP: class P
  let cS: class S
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vy: setvar y
  let cT: class T
  assume lpfval.1: |- X = U. J

  disjoint J x
  disjoint P x
  disjoint S x
  disjoint X x
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint n x
  disjoint n y
  disjoint J n
  disjoint x y
  disjoint J y
  disjoint P n
  disjoint P y
  disjoint S n
  disjoint S y
  disjoint T x
  disjoint X j
  disjoint X n
  disjoint X y
  assert |- ( ( J e. Top /\ S C_ X /\ P e. X ) -> ( P e. ( ( limPt ` J ) ` S ) <-> A. x e. J ( P e. x -> ( x i^i ( S \ { P } ) ) =/= (/) ) ) )

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
    #
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
    cP
    vx
    cv
    #
    wcel
    @8
    @6
    cin
    c0
    wne
    wi
    vx
    cJ
    wral
    #
    @0
    @1
    @4
    @7
    wb
    @2
    cP
    cS
    cJ
    cX
    lpfval.1
    islp
    3adant3
    @0
    @6
    cX
    wss
    @1
    @2
    @7
    @9
    wb
    @3
    cS
    cX
    @5
    @0
    @1
    @2
    simp2
    ssdifssd
    vx
    cP
    @6
    cJ
    cX
    lpfval.1
    elcls
    syld3an2
    bitrd
end
