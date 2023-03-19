include "wfun.mm"
include "cv.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "wrel.mm"
include "dffun6.mm"
include "simplbi.mm"
include "brrelex.mm"
include "ex.mm"
include "syl.mm"
include "ancrd.mm"
include "alrimiv.mm"
include "wceq.mm"
include "breq1.mm"
include "mobidv.mm"
include "imbi2d.mm"
include "simprbi.mm"
include "19.21bi.mm"
include "vtoclg.mm"
include "com12.mm"
include "moanimv.mm"
include "sylibr.mm"
include "moim.mm"
include "sylc.mm"

theorem funmo
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vx: setvar x

  disjoint A y
  disjoint F y
  disjoint x y
  disjoint A x
  disjoint F x
  assert |- ( Fun F -> E* y A F y )

  proof
    cF
    wfun
    #
    cA
    vy
    cv
    #
    cF
    wbr
    #
    cA
    cvv
    wcel
    #
    @2
    wa
    #
    wi
    #
    vy
    wal
    @4
    vy
    wmo
    #
    @2
    vy
    wmo
    #
    @0
    @5
    vy
    @0
    @2
    @3
    @0
    cF
    wrel
    #
    @2
    @3
    wi
    @0
    @8
    vx
    cv
    #
    @1
    cF
    wbr
    #
    vy
    wmo
    #
    vx
    wal
    #
    vx
    vy
    cF
    dffun6
    #
    simplbi
    @8
    @2
    @3
    cA
    @1
    cF
    brrelex
    ex
    syl
    ancrd
    alrimiv
    @0
    @3
    @7
    wi
    @6
    @3
    @0
    @7
    @0
    @11
    wi
    @0
    @7
    wi
    vx
    cA
    cvv
    @9
    cA
    wceq
    #
    @11
    @7
    @0
    @14
    @10
    @2
    vy
    @9
    cA
    @1
    cF
    breq1
    mobidv
    imbi2d
    @0
    @11
    vx
    @0
    @8
    @12
    @13
    simprbi
    19.21bi
    vtoclg
    com12
    @3
    @2
    vy
    moanimv
    sylibr
    @2
    @4
    vy
    moim
    sylc
end
