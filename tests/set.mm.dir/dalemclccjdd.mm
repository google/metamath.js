include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "co.mm"
include "w3a.mm"
include "simp33.mm"
include "sylbi.mm"

theorem dalemclccjdd
  let wps: wff ps
  let cA: class A
  let cC: class C
  let c.or: class .\/
  let c.le: class .<_
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  assume da.ps0: |- ( ps <-> ( ( c e. A /\ d e. A ) /\ -. c .<_ Y /\ ( d =/= c /\ -. d .<_ Y /\ C .<_ ( c .\/ d ) ) ) )


  assert |- ( ps -> C .<_ ( c .\/ d ) )

  proof
    wps
    vc
    cv
    #
    cA
    wcel
    vd
    cv
    #
    cA
    wcel
    wa
    #
    @0
    cY
    c.le
    wbr
    wn
    #
    @1
    @0
    wne
    #
    @1
    cY
    c.le
    wbr
    wn
    #
    cC
    @0
    @1
    c.or
    co
    c.le
    wbr
    #
    w3a
    w3a
    @6
    da.ps0
    @2
    @3
    @4
    @5
    @6
    simp33
    sylbi
end
