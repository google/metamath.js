include "wcel.mm"
include "cn0.mm"
include "wf.mm"
include "w3a.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "creps.mm"
include "cfv.mm"
include "cmpt.mm"
include "ccom.mm"
include "wa.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "repswsymb.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "mpteq2dva.mm"
include "simp3.mm"
include "repsf.mm"
include "3adant3.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "cvv.mm"
include "fvexd.mm"
include "anim1i.mm"
include "reps.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem repsco
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cN: class N
  let vx: setvar x


  assert |- ( ( S e. A /\ N e. NN0 /\ F : A --> B ) -> ( F o. ( S repeatS N ) ) = ( ( F ` S ) repeatS N ) )

  proof
    cS
    cA
    wcel
    #
    cN
    cn0
    wcel
    #
    cA
    cB
    cF
    wf
    #
    w3a
    #
    vx
    cc0
    cN
    cfzo
    co
    #
    vx
    cv
    #
    cS
    cN
    creps
    co
    #
    cfv
    #
    cF
    cfv
    #
    cmpt
    #
    vx
    @4
    cS
    cF
    cfv
    #
    cmpt
    #
    cF
    @6
    ccom
    #
    @10
    cN
    creps
    co
    #
    @3
    vx
    @4
    @8
    @10
    @3
    @5
    @4
    wcel
    #
    wa
    #
    @7
    cS
    cF
    @15
    @0
    @1
    @14
    @7
    cS
    wceq
    @0
    @1
    @2
    @14
    simpl1
    @0
    @1
    @2
    @14
    simpl2
    @3
    @14
    simpr
    cS
    @5
    cN
    cA
    repswsymb
    syl3anc
    fveq2d
    mpteq2dva
    @3
    @2
    @4
    cA
    @6
    wf
    #
    @12
    @9
    wceq
    @0
    @1
    @2
    simp3
    @0
    @1
    @16
    @2
    cS
    cN
    cA
    repsf
    3adant3
    vx
    cF
    @6
    @4
    cA
    cB
    fcompt
    syl2anc
    @3
    @10
    cvv
    wcel
    #
    @1
    wa
    #
    @13
    @11
    wceq
    @0
    @1
    @18
    @2
    @0
    @17
    @1
    @0
    cS
    cF
    fvexd
    anim1i
    3adant3
    vx
    @10
    cN
    cvv
    reps
    syl
    3eqtr4d
end
