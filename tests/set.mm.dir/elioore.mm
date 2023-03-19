include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cxr.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "elioo3g.mm"
include "3ancomb.mm"
include "xrre2.mm"
include "sylanb.mm"
include "sylbi.mm"

theorem elioore
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( A e. ( B (,) C ) -> A e. RR )

  proof
    cA
    cB
    cC
    cioo
    co
    wcel
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    cA
    cxr
    wcel
    #
    w3a
    #
    cB
    cA
    clt
    wbr
    cA
    cC
    clt
    wbr
    wa
    #
    wa
    cA
    cr
    wcel
    #
    cB
    cC
    cA
    elioo3g
    @3
    @0
    @2
    @1
    w3a
    @4
    @5
    @0
    @1
    @2
    3ancomb
    cB
    cA
    cC
    xrre2
    sylanb
    sylbi
end
