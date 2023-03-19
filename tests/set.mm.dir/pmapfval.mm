include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "cpmap.mm"
include "cfv.mm"
include "cbs.mm"
include "cple.mm"
include "catm.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "df-pmap.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem pmapfval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let va: setvar a
  let vk: setvar k
  assume pmapfval.b: |- B = ( Base ` K )
  assume pmapfval.l: |- .<_ = ( le ` K )
  assume pmapfval.a: |- A = ( Atoms ` K )
  assume pmapfval.m: |- M = ( pmap ` K )

  disjoint A a
  disjoint B x
  disjoint a x
  disjoint K a
  disjoint K x
  disjoint a k
  disjoint A k
  disjoint k x
  disjoint B k
  disjoint K k
  disjoint .<_ k
  assert |- ( K e. C -> M = ( x e. B |-> { a e. A | a .<_ x } ) )

  proof
    cK
    cC
    wcel
    cK
    cvv
    wcel
    #
    cM
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
    wceq
    cK
    cC
    elex
    @0
    cM
    cK
    cpmap
    cfv
    @5
    pmapfval.m
    vk
    cK
    vx
    vk
    cv
    #
    cbs
    cfv
    #
    @1
    @2
    @6
    cple
    cfv
    #
    wbr
    #
    va
    @6
    catm
    cfv
    #
    crab
    #
    cmpt
    @5
    cvv
    cpmap
    @6
    cK
    wceq
    #
    vx
    @7
    @11
    cB
    @4
    @12
    @7
    cK
    cbs
    cfv
    #
    cB
    @6
    cK
    cbs
    fveq2
    pmapfval.b
    syl6eqr
    @12
    @9
    @3
    va
    @10
    cA
    @12
    @10
    cK
    catm
    cfv
    cA
    @6
    cK
    catm
    fveq2
    pmapfval.a
    syl6eqr
    @12
    @8
    c.le
    @1
    @2
    @12
    @8
    cK
    cple
    cfv
    c.le
    @6
    cK
    cple
    fveq2
    pmapfval.l
    syl6eqr
    breqd
    rabeqbidv
    mpteq12dv
    vk
    va
    vx
    df-pmap
    vx
    cB
    @4
    cB
    @13
    cvv
    pmapfval.b
    cK
    cbs
    fvex
    eqeltri
    mptex
    fvmpt
    syl5eq
    syl
end
