include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "crn.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "wo.mm"
include "cun.mm"
include "wn.mm"
include "wne.mm"
include "wbr.mm"
include "eqcom.mm"
include "tz6.12i.mm"
include "syl5bi.mm"
include "eximdv.mm"
include "vex.mm"
include "elrn.mm"
include "syl6ibr.mm"
include "com12.mm"
include "necon1bd.mm"
include "velsn.mm"
include "orrd.mm"
include "ss2abi.mm"
include "df-un.mm"
include "sseqtr4i.mm"

theorem fvclss
  let vx: setvar x
  let vy: setvar y
  let cF: class F

  disjoint x y
  disjoint F x
  disjoint F y
  assert |- { y | E. x y = ( F ` x ) } C_ ( ran F u. { (/) } )

  proof
    vy
    cv
    #
    vx
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    wex
    #
    vy
    cab
    @0
    cF
    crn
    #
    wcel
    #
    @0
    c0
    csn
    #
    wcel
    #
    wo
    #
    vy
    cab
    @5
    @7
    cun
    @4
    @9
    vy
    @4
    @6
    @8
    @4
    @6
    wn
    @0
    c0
    wceq
    @8
    @4
    @6
    @0
    c0
    @0
    c0
    wne
    #
    @4
    @6
    @10
    @4
    @1
    @0
    cF
    wbr
    #
    vx
    wex
    @6
    @10
    @3
    @11
    vx
    @3
    @2
    @0
    wceq
    @10
    @11
    @0
    @2
    eqcom
    @1
    @0
    cF
    tz6.12i
    syl5bi
    eximdv
    vx
    @0
    cF
    vy
    vex
    elrn
    syl6ibr
    com12
    necon1bd
    vy
    c0
    velsn
    syl6ibr
    orrd
    ss2abi
    vy
    @5
    @7
    df-un
    sseqtr4i
end
