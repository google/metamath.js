include "cv.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "dalemccea.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"

theorem dalemcceb
  let wps: wff ps
  let cA: class A
  let cC: class C
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  assume da.ps0: |- ( ps <-> ( ( c e. A /\ d e. A ) /\ -. c .<_ Y /\ ( d =/= c /\ -. d .<_ Y /\ C .<_ ( c .\/ d ) ) ) )
  assume da.a1: |- A = ( Atoms ` K )


  assert |- ( ps -> c e. ( Base ` K ) )

  proof
    wps
    vc
    cv
    #
    cA
    wcel
    @0
    cK
    cbs
    cfv
    #
    wcel
    wps
    cA
    cC
    c.or
    c.le
    cY
    vc
    vd
    da.ps0
    dalemccea
    cA
    @1
    @0
    cK
    @1
    eqid
    da.a1
    atbase
    syl
end
