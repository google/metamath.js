include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cmpt.mm"
include "pmapfval.mm"
include "fveq1d.mm"
include "wceq.mm"
include "breq2.mm"
include "rabbidv.mm"
include "eqid.mm"
include "catm.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem pmapval
  let cA: class A
  let cB: class B
  let cC: class C
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let cX: class X
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  let cP: class P
  assume pmapfval.b: |- B = ( Base ` K )
  assume pmapfval.l: |- .<_ = ( le ` K )
  assume pmapfval.a: |- A = ( Atoms ` K )
  assume pmapfval.m: |- M = ( pmap ` K )

  disjoint A a
  disjoint K a
  disjoint X a
  disjoint a k
  disjoint A k
  disjoint k x
  disjoint B k
  disjoint B x
  disjoint a x
  disjoint K k
  disjoint K x
  disjoint .<_ k
  disjoint A x
  disjoint .<_ x
  disjoint X x
  disjoint P x
  assert |- ( ( K e. C /\ X e. B ) -> ( M ` X ) = { a e. A | a .<_ X } )

  proof
    cK
    cC
    wcel
    #
    cX
    cB
    wcel
    cX
    cM
    cfv
    cX
    vx
    cB
    va
    cv
    #
    vx
    cv
    #
    c.le
    wbr
    #
    va
    cA
    crab
    #
    cmpt
    #
    cfv
    @1
    cX
    c.le
    wbr
    #
    va
    cA
    crab
    #
    @0
    cX
    cM
    @5
    vx
    cA
    cB
    cC
    cK
    c.le
    cM
    va
    pmapfval.b
    pmapfval.l
    pmapfval.a
    pmapfval.m
    pmapfval
    fveq1d
    vx
    cX
    @4
    @7
    cB
    @5
    @2
    cX
    wceq
    @3
    @6
    va
    cA
    @2
    cX
    @1
    c.le
    breq2
    rabbidv
    @5
    eqid
    @6
    va
    cA
    cA
    cK
    catm
    cfv
    cvv
    pmapfval.a
    cK
    catm
    fvex
    eqeltri
    rabex
    fvmpt
    sylan9eq
end
