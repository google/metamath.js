include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "restval.mm"
include "wf.mm"
include "wss.mm"
include "filin.mm"
include "3expa.mm"
include "an32s.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "eqsstrd.mm"

theorem trfilss
  let cA: class A
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cV: class V


  assert |- ( ( F e. ( Fil ` X ) /\ A e. F ) -> ( F |`t A ) C_ F )

  proof
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cA
    cF
    wcel
    #
    wa
    #
    cF
    cA
    crest
    co
    vx
    cF
    vx
    cv
    #
    cA
    cin
    #
    cmpt
    #
    crn
    #
    cF
    vx
    cA
    cF
    @0
    cF
    restval
    @3
    cF
    cF
    @6
    wf
    @7
    cF
    wss
    @3
    vx
    cF
    @5
    cF
    @6
    @1
    @4
    cF
    wcel
    #
    @2
    @5
    cF
    wcel
    #
    @1
    @8
    @2
    @9
    @4
    cA
    cF
    cX
    filin
    3expa
    an32s
    @6
    eqid
    fmptd
    cF
    cF
    @6
    frn
    syl
    eqsstrd
end
