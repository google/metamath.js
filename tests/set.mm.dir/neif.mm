include "ctop.mm"
include "wcel.mm"
include "cnei.mm"
include "cfv.mm"
include "cpw.mm"
include "wfn.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "crab.mm"
include "cmpt.mm"
include "cvv.mm"
include "wral.mm"
include "topopn.mm"
include "pwexg.mm"
include "rabexg.mm"
include "3syl.mm"
include "ralrimivw.mm"
include "eqid.mm"
include "fnmpt.mm"
include "syl.mm"
include "neifval.mm"
include "fneq1d.mm"
include "mpbird.mm"

theorem neif
  let cJ: class J
  let cX: class X
  let vg: setvar g
  let vj: setvar j
  let vv: setvar v
  let vx: setvar x
  let cN: class N
  let cP: class P
  let cS: class S
  assume neifval.1: |- X = U. J


  assert |- ( J e. Top -> ( nei ` J ) Fn ~P X )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    cnei
    cfv
    #
    cX
    cpw
    #
    wfn
    vx
    @2
    vx
    cv
    vg
    cv
    #
    wss
    @3
    vv
    cv
    wss
    wa
    vg
    cJ
    wrex
    #
    vv
    @2
    crab
    #
    cmpt
    #
    @2
    wfn
    #
    @0
    @5
    cvv
    wcel
    #
    vx
    @2
    wral
    @7
    @0
    @8
    vx
    @2
    @0
    cX
    cJ
    wcel
    @2
    cvv
    wcel
    @8
    cJ
    cX
    neifval.1
    topopn
    cX
    cJ
    pwexg
    @4
    vv
    @2
    cvv
    rabexg
    3syl
    ralrimivw
    vx
    @2
    @5
    @6
    cvv
    @6
    eqid
    fnmpt
    syl
    @0
    @2
    @1
    @6
    vx
    vv
    vg
    cJ
    cX
    neifval.1
    neifval
    fneq1d
    mpbird
end
