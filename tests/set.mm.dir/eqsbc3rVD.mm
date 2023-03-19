include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wsbc.mm"
include "wb.mm"
include "wi.mm"
include "idn1.mm"
include "eqsbc3.mm"
include "e1a.mm"
include "eqcom.mm"
include "sbcbiiOLD.mm"
include "idn2.mm"
include "biimp.mm"
include "e12.mm"
include "e2bi.mm"
include "in2.mm"
include "e2bir.mm"
include "biimpr.mm"
include "impbi.mm"
include "e11.mm"
include "in1.mm"

theorem eqsbc3rVD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint C x
  assert |- ( A e. B -> ( [. A / x ]. C = x <-> C = A ) )

  proof
    cA
    cB
    wcel
    #
    cC
    vx
    cv
    #
    wceq
    #
    vx
    cA
    wsbc
    #
    cC
    cA
    wceq
    #
    wb
    #
    @0
    @3
    @4
    wi
    @4
    @3
    wi
    @5
    @0
    @3
    @4
    @0
    @3
    cA
    cC
    wceq
    #
    @4
    @0
    @1
    cC
    wceq
    #
    vx
    cA
    wsbc
    #
    @6
    wb
    #
    @3
    @8
    @6
    @0
    @0
    @9
    @0
    idn1
    #
    vx
    cA
    cC
    cB
    eqsbc3
    e1a
    #
    @0
    @3
    @8
    wb
    #
    @3
    @3
    @8
    @0
    @0
    @12
    @10
    @2
    @7
    vx
    cA
    cB
    cC
    @1
    eqcom
    sbcbiiOLD
    e1a
    #
    @0
    @3
    idn2
    @3
    @8
    biimp
    e12
    @8
    @6
    biimp
    e12
    cA
    cC
    eqcom
    #
    e2bi
    in2
    @0
    @4
    @3
    @0
    @12
    @4
    @8
    @3
    @13
    @0
    @9
    @4
    @6
    @8
    @11
    @0
    @4
    @4
    @6
    @0
    @4
    idn2
    @14
    e2bir
    @8
    @6
    biimpr
    e12
    @3
    @8
    biimpr
    e12
    in2
    @3
    @4
    impbi
    e11
    in1
end
