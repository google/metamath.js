include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "clsss3.mm"
include "ssel.mm"
include "pm4.71rd.mm"
include "syl.mm"
include "elcls.mm"
include "3expa.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem elcls2
  let vx: setvar x
  let cP: class P
  let cS: class S
  let cJ: class J
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J

  disjoint J x
  disjoint P x
  disjoint S x
  disjoint X x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint S y
  disjoint S z
  disjoint U x
  disjoint X y
  disjoint X z
  disjoint T x
  disjoint A x
  assert |- ( ( J e. Top /\ S C_ X ) -> ( P e. ( ( cls ` J ) ` S ) <-> ( P e. X /\ A. x e. J ( P e. x -> ( x i^i S ) =/= (/) ) ) ) )

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
    ccl
    cfv
    cfv
    #
    wcel
    #
    cP
    cX
    wcel
    #
    @4
    wa
    #
    @5
    cP
    vx
    cv
    #
    wcel
    @7
    cS
    cin
    c0
    wne
    wi
    vx
    cJ
    wral
    #
    wa
    @2
    @3
    cX
    wss
    #
    @4
    @6
    wb
    cS
    cJ
    cX
    clscld.1
    clsss3
    @9
    @4
    @5
    @3
    cX
    cP
    ssel
    pm4.71rd
    syl
    @2
    @5
    @4
    @8
    @0
    @1
    @5
    @4
    @8
    wb
    vx
    cP
    cS
    cJ
    cX
    clscld.1
    elcls
    3expa
    pm5.32da
    bitrd
end
