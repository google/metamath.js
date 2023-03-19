include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cioo.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cle.mm"
include "wn.mm"
include "ioo0.mm"
include "wb.mm"
include "xrlenlt.mm"
include "ancoms.mm"
include "bitr2d.mm"
include "necon1abid.mm"

theorem ioon0
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( ( A (,) B ) =/= (/) <-> A < B ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    cA
    cB
    cioo
    co
    #
    c0
    @2
    @4
    c0
    wceq
    cB
    cA
    cle
    wbr
    #
    @3
    wn
    #
    cA
    cB
    ioo0
    @1
    @0
    @5
    @6
    wb
    cB
    cA
    xrlenlt
    ancoms
    bitr2d
    necon1abid
end
