include "c0.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "csuc.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "con0.mm"
include "wcel.mm"
include "0elon.mm"
include "oa0.mm"
include "ax-mp.mm"
include "com.mm"
include "peano1.mm"
include "nnasuc.mm"
include "mpan.mm"
include "suceq.mm"
include "eqeq2d.mm"
include "syl5ibcom.mm"
include "finds.mm"

theorem nna0r
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( A e. _om -> ( (/) +o A ) = A )

  proof
    c0
    vx
    cv
    #
    coa
    co
    #
    @0
    wceq
    c0
    c0
    coa
    co
    #
    c0
    wceq
    #
    c0
    vy
    cv
    #
    coa
    co
    #
    @4
    wceq
    #
    c0
    @4
    csuc
    #
    coa
    co
    #
    @7
    wceq
    #
    c0
    cA
    coa
    co
    #
    cA
    wceq
    vx
    vy
    cA
    @0
    c0
    wceq
    #
    @1
    @2
    @0
    c0
    @0
    c0
    c0
    coa
    oveq2
    @11
    id
    eqeq12d
    @0
    @4
    wceq
    #
    @1
    @5
    @0
    @4
    @0
    @4
    c0
    coa
    oveq2
    @12
    id
    eqeq12d
    @0
    @7
    wceq
    #
    @1
    @8
    @0
    @7
    @0
    @7
    c0
    coa
    oveq2
    @13
    id
    eqeq12d
    @0
    cA
    wceq
    #
    @1
    @10
    @0
    cA
    @0
    cA
    c0
    coa
    oveq2
    @14
    id
    eqeq12d
    c0
    con0
    wcel
    @3
    0elon
    c0
    oa0
    ax-mp
    @4
    com
    wcel
    #
    @8
    @5
    csuc
    #
    wceq
    #
    @6
    @9
    c0
    com
    wcel
    @15
    @17
    peano1
    c0
    @4
    nnasuc
    mpan
    @6
    @16
    @7
    @8
    @5
    @4
    suceq
    eqeq2d
    syl5ibcom
    finds
end
