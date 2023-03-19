include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "co.mm"
include "w3a.mm"
include "simp1r.mm"
include "sylbi.mm"

theorem dalemddea
  let wps: wff ps
  let cA: class A
  let cC: class C
  let c.or: class .\/
  let c.le: class .<_
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  assume da.ps0: |- ( ps <-> ( ( c e. A /\ d e. A ) /\ -. c .<_ Y /\ ( d =/= c /\ -. d .<_ Y /\ C .<_ ( c .\/ d ) ) ) )


  assert |- ( ps -> d e. A )

  proof
    wps
    vc
    cv
    #
    cA
    wcel
    #
    vd
    cv
    #
    cA
    wcel
    #
    wa
    @0
    cY
    c.le
    wbr
    wn
    #
    @2
    @0
    wne
    @2
    cY
    c.le
    wbr
    wn
    cC
    @0
    @2
    c.or
    co
    c.le
    wbr
    w3a
    #
    w3a
    @3
    da.ps0
    @1
    @3
    @4
    @5
    simp1r
    sylbi
end
