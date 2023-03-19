include "cv.mm"
include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "copab.mm"
include "c3.mm"
include "c4.mm"
include "wbr.mm"
include "3cn.mm"
include "4cn.mm"
include "3p1e4.mm"
include "elexi.mm"
include "eleq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "3anbi13d.mm"
include "eqeq2.mm"
include "3anbi23d.mm"
include "eqid.mm"
include "brab.mm"
include "mpbir3an.mm"
include "breq.mm"
include "mpbiri.mm"

theorem ex-opab
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint x y
  assert |- ( R = { <. x , y >. | ( x e. CC /\ y e. CC /\ ( x + 1 ) = y ) } -> 3 R 4 )

  proof
    cR
    vx
    cv
    #
    cc
    wcel
    #
    vy
    cv
    #
    cc
    wcel
    #
    @0
    c1
    caddc
    co
    #
    @2
    wceq
    #
    w3a
    #
    vx
    vy
    copab
    #
    wceq
    c3
    c4
    cR
    wbr
    c3
    c4
    @7
    wbr
    #
    @8
    c3
    cc
    wcel
    #
    c4
    cc
    wcel
    #
    c3
    c1
    caddc
    co
    #
    c4
    wceq
    #
    3cn
    4cn
    3p1e4
    @6
    @9
    @3
    @11
    @2
    wceq
    #
    w3a
    @9
    @10
    @12
    w3a
    vx
    vy
    c3
    c4
    @7
    c3
    cc
    3cn
    elexi
    c4
    cc
    4cn
    elexi
    @0
    c3
    wceq
    #
    @1
    @9
    @5
    @13
    @3
    @0
    c3
    cc
    eleq1
    @14
    @4
    @11
    @2
    @0
    c3
    c1
    caddc
    oveq1
    eqeq1d
    3anbi13d
    @2
    c4
    wceq
    @3
    @10
    @13
    @12
    @9
    @2
    c4
    cc
    eleq1
    @2
    c4
    @11
    eqeq2
    3anbi23d
    @7
    eqid
    brab
    mpbir3an
    c3
    c4
    cR
    @7
    breq
    mpbiri
end
