include "wcel.mm"
include "cn0.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "w3a.mm"
include "creps.mm"
include "cmpt.mm"
include "wceq.mm"
include "reps.mm"
include "3adant3.mm"
include "cv.mm"
include "wa.mm"
include "eqidd.mm"
include "simp3.mm"
include "simp1.mm"
include "fvmptd.mm"

theorem repswsymb
  let cS: class S
  let cI: class I
  let cN: class N
  let cV: class V
  let vx: setvar x


  assert |- ( ( S e. V /\ N e. NN0 /\ I e. ( 0 ..^ N ) ) -> ( ( S repeatS N ) ` I ) = S )

  proof
    cS
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    cI
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    vx
    cI
    cS
    cS
    @2
    cS
    cN
    creps
    co
    #
    cV
    @0
    @1
    @5
    vx
    @2
    cS
    cmpt
    wceq
    @3
    vx
    cS
    cN
    cV
    reps
    3adant3
    @4
    vx
    cv
    cI
    wceq
    wa
    cS
    eqidd
    @0
    @1
    @3
    simp3
    @0
    @1
    @3
    simp1
    fvmptd
end
