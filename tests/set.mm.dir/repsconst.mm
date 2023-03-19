include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "creps.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "reps.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"

theorem repsconst
  let cS: class S
  let cN: class N
  let cV: class V
  let vx: setvar x


  assert |- ( ( S e. V /\ N e. NN0 ) -> ( S repeatS N ) = ( ( 0 ..^ N ) X. { S } ) )

  proof
    cS
    cV
    wcel
    cN
    cn0
    wcel
    wa
    cS
    cN
    creps
    co
    vx
    cc0
    cN
    cfzo
    co
    #
    cS
    cmpt
    @0
    cS
    csn
    cxp
    vx
    cS
    cN
    cV
    reps
    vx
    @0
    cS
    fconstmpt
    syl6eqr
end
