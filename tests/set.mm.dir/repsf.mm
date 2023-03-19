include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "creps.mm"
include "wf.mm"
include "cmpt.mm"
include "wral.mm"
include "cv.mm"
include "simpl.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "reps.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem repsf
  let cS: class S
  let cN: class N
  let cV: class V
  let vx: setvar x


  assert |- ( ( S e. V /\ N e. NN0 ) -> ( S repeatS N ) : ( 0 ..^ N ) --> V )

  proof
    cS
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cc0
    cN
    cfzo
    co
    #
    cV
    cS
    cN
    creps
    co
    #
    wf
    @3
    cV
    vx
    @3
    cS
    cmpt
    #
    wf
    #
    @2
    @0
    vx
    @3
    wral
    #
    @6
    @0
    @7
    @1
    @0
    @0
    vx
    @3
    @0
    vx
    cv
    @3
    wcel
    simpl
    ralrimiva
    adantr
    vx
    @3
    cV
    cS
    @5
    @5
    eqid
    fmpt
    sylib
    @2
    @3
    cV
    @4
    @5
    vx
    cS
    cN
    cV
    reps
    feq1d
    mpbird
end
