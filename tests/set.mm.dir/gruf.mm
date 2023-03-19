include "cgru.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt.mm"
include "crn.mm"
include "simp3.mm"
include "feqmptd.mm"
include "fvex.mm"
include "fnasrn.mm"
include "syl6eq.mm"
include "wa.mm"
include "simpl1.mm"
include "gruel.mm"
include "3expa.mm"
include "3adantl3.mm"
include "ffvelrn.mm"
include "3ad2antl3.mm"
include "gruop.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "grurn.mm"
include "syld3an3.mm"
include "eqeltrd.mm"

theorem gruf
  let cA: class A
  let cU: class U
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( ( U e. Univ /\ A e. U /\ F : A --> U ) -> F e. U )

  proof
    cU
    cgru
    wcel
    #
    cA
    cU
    wcel
    #
    cA
    cU
    cF
    wf
    #
    w3a
    #
    cF
    vx
    cA
    vx
    cv
    #
    @4
    cF
    cfv
    #
    cop
    #
    cmpt
    #
    crn
    #
    cU
    @3
    cF
    vx
    cA
    @5
    cmpt
    @8
    @3
    vx
    cA
    cU
    cF
    @0
    @1
    @2
    simp3
    feqmptd
    vx
    cA
    @5
    @4
    cF
    fvex
    fnasrn
    syl6eq
    @0
    @1
    @2
    cA
    cU
    @7
    wf
    @8
    cU
    wcel
    @3
    vx
    cA
    @6
    cU
    @7
    @3
    @4
    cA
    wcel
    #
    wa
    @0
    @4
    cU
    wcel
    #
    @5
    cU
    wcel
    #
    @6
    cU
    wcel
    @0
    @1
    @2
    @9
    simpl1
    @0
    @1
    @9
    @10
    @2
    @0
    @1
    @9
    @10
    cA
    @4
    cU
    gruel
    3expa
    3adantl3
    @2
    @0
    @9
    @11
    @1
    cA
    cU
    @4
    cF
    ffvelrn
    3ad2antl3
    @4
    @5
    cU
    gruop
    syl3anc
    @7
    eqid
    fmptd
    cA
    cU
    @7
    grurn
    syld3an3
    eqeltrd
end
