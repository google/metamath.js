include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "xmetge0.mm"
include "biantrud.mm"
include "cxr.mm"
include "wb.mm"
include "xmetcl.mm"
include "0xr.mm"
include "xrletri3.mm"
include "sylancl.mm"
include "bitr4d.mm"
include "xrlenlt.mm"
include "xmeteq0.mm"
include "3bitr3d.mm"
include "necon1abid.mm"

theorem xmetgt0
  let cA: class A
  let cB: class B
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vd: setvar d
  let vw: setvar w
  let cR: class R
  let cC: class C


  assert |- ( ( D e. ( *Met ` X ) /\ A e. X /\ B e. X ) -> ( A =/= B <-> 0 < ( A D B ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    cA
    cX
    wcel
    cB
    cX
    wcel
    w3a
    #
    cc0
    cA
    cB
    cD
    co
    #
    clt
    wbr
    #
    cA
    cB
    @0
    @1
    cc0
    cle
    wbr
    #
    @1
    cc0
    wceq
    #
    @2
    wn
    #
    cA
    cB
    wceq
    @0
    @3
    @3
    cc0
    @1
    cle
    wbr
    #
    wa
    #
    @4
    @0
    @6
    @3
    cA
    cB
    cD
    cX
    xmetge0
    biantrud
    @0
    @1
    cxr
    wcel
    #
    cc0
    cxr
    wcel
    #
    @4
    @7
    wb
    cA
    cB
    cD
    cX
    xmetcl
    #
    0xr
    @1
    cc0
    xrletri3
    sylancl
    bitr4d
    @0
    @8
    @9
    @3
    @5
    wb
    @10
    0xr
    @1
    cc0
    xrlenlt
    sylancl
    cA
    cB
    cD
    cX
    xmeteq0
    3bitr3d
    necon1abid
end
