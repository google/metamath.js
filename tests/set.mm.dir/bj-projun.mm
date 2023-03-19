include "cun.mm"
include "bj-cproj.mm"
include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "csn.mm"
include "cima.mm"
include "df-bj-proj.mm"
include "abeq2i.mm"
include "orbi12i.mm"
include "elun.mm"
include "imaundir.mm"
include "eleq2i.mm"
include "3bitri.mm"
include "3bitr4ri.mm"
include "eqriv.mm"

theorem bj-projun
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A Proj ( B u. C ) ) = ( ( A Proj B ) u. ( A Proj C ) )

  proof
    vx
    cA
    cB
    cC
    cun
    #
    bj-cproj
    #
    cA
    cB
    bj-cproj
    #
    cA
    cC
    bj-cproj
    #
    cun
    #
    vx
    cv
    #
    @2
    wcel
    #
    @5
    @3
    wcel
    #
    wo
    @5
    csn
    #
    cB
    cA
    csn
    #
    cima
    #
    wcel
    #
    @8
    cC
    @9
    cima
    #
    wcel
    #
    wo
    #
    @5
    @4
    wcel
    @5
    @1
    wcel
    #
    @6
    @11
    @7
    @13
    @11
    vx
    @2
    vx
    cA
    cB
    df-bj-proj
    abeq2i
    @13
    vx
    @3
    vx
    cA
    cC
    df-bj-proj
    abeq2i
    orbi12i
    @5
    @2
    @3
    elun
    @15
    @8
    @0
    @9
    cima
    #
    wcel
    #
    @8
    @10
    @12
    cun
    #
    wcel
    @14
    @17
    vx
    @1
    vx
    cA
    @0
    df-bj-proj
    abeq2i
    @16
    @18
    @8
    cB
    cC
    @9
    imaundir
    eleq2i
    @8
    @10
    @12
    elun
    3bitri
    3bitr4ri
    eqriv
end
