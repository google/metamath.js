include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "co.mm"
include "w3a.mm"
include "simp31.mm"
include "sylbi.mm"
include "necomd.mm"

theorem dalemccnedd
  let wps: wff ps
  let cA: class A
  let cC: class C
  let c.or: class .\/
  let c.le: class .<_
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  assume da.ps0: |- ( ps <-> ( ( c e. A /\ d e. A ) /\ -. c .<_ Y /\ ( d =/= c /\ -. d .<_ Y /\ C .<_ ( c .\/ d ) ) ) )


  assert |- ( ps -> c =/= d )

  proof
    wps
    vd
    cv
    #
    vc
    cv
    #
    wps
    @1
    cA
    wcel
    @0
    cA
    wcel
    wa
    #
    @1
    cY
    c.le
    wbr
    wn
    #
    @0
    @1
    wne
    #
    @0
    cY
    c.le
    wbr
    wn
    #
    cC
    @1
    @0
    c.or
    co
    c.le
    wbr
    #
    w3a
    w3a
    @4
    da.ps0
    @2
    @3
    @4
    @5
    @6
    simp31
    sylbi
    necomd
end
