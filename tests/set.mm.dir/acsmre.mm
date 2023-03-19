include "cacs.mm"
include "cfv.mm"
include "wcel.mm"
include "cmre.mm"
include "cpw.mm"
include "cv.mm"
include "wf.mm"
include "cfn.mm"
include "cin.mm"
include "cima.mm"
include "cuni.mm"
include "wss.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "isacs.mm"
include "simplbi.mm"

theorem acsmre
  let cC: class C
  let cX: class X
  let vc: setvar c
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  let cF: class F
  let vz: setvar z
  let cS: class S
  let vx: setvar x


  assert |- ( C e. ( ACS ` X ) -> C e. ( Moore ` X ) )

  proof
    cC
    cX
    cacs
    cfv
    wcel
    cC
    cX
    cmre
    cfv
    wcel
    cX
    cpw
    #
    @0
    vf
    cv
    #
    wf
    vs
    cv
    #
    cC
    wcel
    @1
    @2
    cpw
    cfn
    cin
    cima
    cuni
    @2
    wss
    wb
    vs
    @0
    wral
    wa
    vf
    wex
    cC
    vf
    cX
    vs
    isacs
    simplbi
end
