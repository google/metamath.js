include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "pmapval.mm"
include "eleq2d.mm"
include "breq1.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem elpmap
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let cX: class X
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  assume pmapfval.b: |- B = ( Base ` K )
  assume pmapfval.l: |- .<_ = ( le ` K )
  assume pmapfval.a: |- A = ( Atoms ` K )
  assume pmapfval.m: |- M = ( pmap ` K )


  assert |- ( ( K e. C /\ X e. B ) -> ( P e. ( M ` X ) <-> ( P e. A /\ P .<_ X ) ) )

  proof
    cK
    cC
    wcel
    cX
    cB
    wcel
    wa
    #
    cP
    cX
    cM
    cfv
    #
    wcel
    cP
    vx
    cv
    #
    cX
    c.le
    wbr
    #
    vx
    cA
    crab
    #
    wcel
    cP
    cA
    wcel
    cP
    cX
    c.le
    wbr
    #
    wa
    @0
    @1
    @4
    cP
    cA
    cB
    cC
    cK
    c.le
    cM
    cX
    vx
    pmapfval.b
    pmapfval.l
    pmapfval.a
    pmapfval.m
    pmapval
    eleq2d
    @3
    @5
    vx
    cP
    cA
    @2
    cP
    cX
    c.le
    breq1
    elrab
    syl6bb
end
