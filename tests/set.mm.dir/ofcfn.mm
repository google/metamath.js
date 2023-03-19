include "cofc.mm"
include "co.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "ovex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "ofcfval.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem ofcfn
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let vc: setvar c
  let vf: setvar f
  let vx: setvar x
  assume ofcfval.1: |- ( ph -> F Fn A )
  assume ofcfval.2: |- ( ph -> A e. V )
  assume ofcfval.3: |- ( ph -> C e. W )


  assert |- ( ph -> ( F oFC R C ) Fn A )

  proof
    wph
    cF
    cC
    cR
    cofc
    co
    #
    cA
    wfn
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cC
    cR
    co
    #
    cmpt
    #
    cA
    wfn
    vx
    cA
    @3
    @4
    @2
    cC
    cR
    ovex
    @4
    eqid
    fnmpti
    wph
    cA
    @0
    @4
    wph
    vx
    cA
    @2
    cC
    cR
    cF
    cV
    cW
    ofcfval.1
    ofcfval.2
    ofcfval.3
    wph
    @1
    cA
    wcel
    wa
    @2
    eqidd
    ofcfval
    fneq1d
    mpbiri
end
