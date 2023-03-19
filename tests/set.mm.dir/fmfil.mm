include "wcel.mm"
include "cfbas.mm"
include "cfv.mm"
include "wf.mm"
include "w3a.mm"
include "cfm.mm"
include "co.mm"
include "cv.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cfg.mm"
include "cfil.mm"
include "fmval.mm"
include "eqid.mm"
include "fbasrn.mm"
include "3comr.mm"
include "fgcl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem fmfil
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( X e. A /\ B e. ( fBas ` Y ) /\ F : Y --> X ) -> ( ( X FilMap F ) ` B ) e. ( Fil ` X ) )

  proof
    cX
    cA
    wcel
    #
    cB
    cY
    cfbas
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cB
    cX
    cF
    cfm
    co
    cfv
    cX
    vy
    cB
    cF
    vy
    cv
    cima
    cmpt
    crn
    #
    cfg
    co
    #
    cX
    cfil
    cfv
    #
    vy
    cA
    cB
    cF
    cX
    cY
    fmval
    @3
    @4
    cX
    cfbas
    cfv
    wcel
    #
    @5
    @6
    wcel
    @1
    @2
    @0
    @7
    vy
    cB
    @4
    cF
    cA
    cY
    cX
    @4
    eqid
    fbasrn
    3comr
    @4
    cX
    fgcl
    syl
    eqeltrd
end
