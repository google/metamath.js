include "cvv.mm"
include "cv.mm"
include "cprds.mm"
include "co.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "cfn.mm"
include "wcel.mm"
include "cbs.mm"
include "cixp.mm"
include "cress.mm"
include "cdsmm.mm"
include "df-dsmm.mm"
include "reldmmpt2.mm"

theorem reldmdsmm
  let cS: class S
  let vs: setvar s
  let vr: setvar r
  let vf: setvar f
  let vx: setvar x
  let cR: class R
  let cB: class B


  assert |- Rel dom (+)m

  proof
    vs
    vr
    cvv
    cvv
    vs
    cv
    vr
    cv
    #
    cprds
    co
    vx
    cv
    #
    vf
    cv
    cfv
    @1
    @0
    cfv
    #
    c0g
    cfv
    wne
    vx
    @0
    cdm
    #
    crab
    cfn
    wcel
    vf
    vx
    @3
    @2
    cbs
    cfv
    cixp
    crab
    cress
    co
    cdsmm
    vx
    vf
    vs
    vr
    df-dsmm
    reldmmpt2
end
